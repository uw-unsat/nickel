#include <assert.h>
#include <fcntl.h>
#include <nistar/libfs.h>
#include <nistar/memlayout.h>
#include <nistar/env.h>
#include <stdarg.h>
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>

#define check(a) {{ long ret = (a); if (ret) return ret; }}
#define DIRSIZ PAGE_NAME_LEN

struct inode {
        usymlink_t inum;
        size_t fsize;
        mode_t mode;

        int atime;
        int mtime;
        int ctime;

        /* TODO: we can keep a refcnt here for number of open references to the
         * file, to ensure posix semantics for deletion.

           When a proc deletes a file, if the refcnt is non-zero the fs creates
           a deletion gate to delegate the deletion to the holder of the last
           reference.  */
        uint64_t ref;
};

struct dinode {
        size_t fsize;
        mode_t mode;
        int atime;
        int mtime;
        int ctime;
};

struct file {
        /* sym to the open object */
        struct inode *ino;

        void *base;
        off_t offset;
        size_t size;
        int flags;
};

static usymlink_t fs_get_root_container()
{
        static usymlink_t fs_root = USYMLINK_INVALID;
        if (!usymlink_is_valid(fs_root)) {
                char name[PAGE_NAME_LEN];
                size_t i;
                usymlink_t root = container_get_root();
                for (i = 0; i < CONTAINER_NR_PAGES; i++)
                        if (container_get_slot(root, i, &fs_root) == 0) {
                                ASSERT_MSG(page_get_name(fs_root, name) == 0, "page_get_name");
                                if (name[0] == '/' && name[1] == 0)
                                        goto found;
                        }
                ASSERT_MSG(false, "Could not find fs root\n");
        }
found:
        return fs_root;
}

static struct file *file_table = (void *)FS_FILE_STRUCT_START;
static struct inode *inodes = (void *)FS_FILE_INODE_START;

static void get_dinode(usymlink_t usym, struct dinode *dip)
{
        ASSERT_MSG(sizeof(struct dinode) <= PAGE_METADATA_LEN,
                   "dinode too large");
        char page_meta[PAGE_METADATA_LEN];
        ASSERT_MSG(page_get_metadata(usym, page_meta) == 0,
                        "could not get metadata");
        memcpy(dip, page_meta, sizeof(struct dinode));
}

static void put_dinode(usymlink_t usym, struct dinode *dip)
{
        long r;
        ASSERT_MSG(sizeof(struct dinode) <= PAGE_METADATA_LEN,
                   "dinode too large");
        char page_meta[PAGE_METADATA_LEN];
        memset(page_meta, 0, sizeof(page_meta));
        memcpy(page_meta, dip, sizeof(struct dinode));
        r = page_set_metadata(usym, page_meta);
        ASSERT_MSG(r == 0 || r == -EACCES,
                   "could not set metadata");
}

static struct inode *ialloc(size_t i)
{
        for (; i < NFILES; i++)
                if (inodes[i].ref == 0) {
                        memset(&inodes[i], 0, sizeof(struct inode));
                        return &inodes[i];
                }
        panic("alloc: ran out of inodes");
}

static void isync(struct inode *ip)
{
        struct dinode di;
        di.fsize = ip->fsize;
        di.mode = ip->mode;
        di.atime = ip->atime;
        di.mtime = ip->mtime;
        di.ctime = ip->ctime;
        put_dinode(ip->inum, &di);
}

static struct inode *iget(usymlink_t usym)
{
        size_t i;
        struct inode *ip = NULL;

        struct dinode di;

        for (i = 0; i < NFILES; i++) {
                if (usymlink_eq(inodes[i].inum, usym)) {
                        ip = &inodes[i];
                }
        }

        if (ip == NULL) {
                get_dinode(usym, &di);
                ip = ialloc(0);
                ip->inum = usym;
                ip->fsize = di.fsize;
                ip->mode = di.mode;
                ip->atime = di.atime;
                ip->ctime = di.ctime;
        }

        ip->ref++;
        return ip;
}

static void iput(struct inode *ip)
{
        ASSERT_MSG(ip->ref > 0, "iput: refcount has to be non-zero");
        ip->ref--;
        isync(ip);
        if (ip->ref == 0) {
                memset(ip, 0, sizeof(struct inode));
        }
}

static void incref(struct inode *ip)
{
        ASSERT_MSG(ip->ref > 0, "incref: refcount has to be non-zero");
        ip->ref++;
        isync(ip);
}

static int find_free_fd(size_t i)
{
        for (; i < NFILES; i++)
                if (file_table[i].ino == NULL)
                        return i;
        ASSERT_MSG(false, "File table full\n");
        return -EMFILE;
}

static inline int fd_is_valid(int fd)
{
        return (fd >= 0 && fd < NFILES);
}

static inline int fd_is_open(int fd)
{
        return fd_is_valid(fd) &&
               file_table[fd].ino != NULL &&
               file_table[fd].ino->mode != 0;
}

static inline int fd_is_mode(int fd, mode_t mode)
{
        return fd_is_valid(fd) && (file_table[fd].ino->mode & S_IFMT) == mode;
}

static inline int fd_is_readable(int fd)
{
        if (!fd_is_open(fd))
                return false;
        int accmode = file_table[fd].flags & O_ACCMODE;
        return accmode == O_RDONLY || accmode == O_RDWR;
}

static inline int fd_is_writable(int fd)
{

        if (!fd_is_open(fd))
                return false;
        int accmode = file_table[fd].flags & O_ACCMODE;
        return accmode == O_WRONLY || accmode == O_RDWR;
}

static int namecmp(const char *s, const char *t)
{
    return strncmp(s, t, DIRSIZ);
}

static int map_file(int fd)
{
        ASSERT_MSG(fd_is_mode(fd, S_IFREG), "fd %d is not associated with an open file");
        struct file *f = &file_table[fd];
        f->base = (void *)FS_FILE_MAP_START + (uint64_t)fd * SZ_1G;
        usymlink_t pud = self_get_pud();
        ASSERT_MSG(directory_link_pmd(pud, pdpt_index((uintptr_t)f->base), f->ino->inum) == 0, "directory_link_pmd");

        return 0;
}

static size_t file_size(usymlink_t usym)
{
        uint64_t type;
        size_t n = 0;
        usymlink_t blk;
        ASSERT_MSG(page_get_type(usym, &type) == 0, "page_get_size");

        switch (type) {
                case PAGE_TYPE_CONTAINER:
                        return CONTAINER_NR_PAGES;
                case PAGE_TYPE_GATE:
                        return 0;
                case PAGE_TYPE_PMD:
                        while (directory_get_slot(usym, n, &blk) == 0) n++;
                        return n * SZ_2M;
        }
        panic("File type unrecognized");
}

// Copy the next path element from path into name.
// Return a pointer to the element following the copied one.
// The returned path has no leading slashes,
// so the caller can check *path=='\0' to see if the name is the last one.
// If no name to remove, return 0.
//
// Examples:
//   skipelem("a/bb/c", name) = "bb/c", setting name = "a"
//   skipelem("///a//bb", name) = "bb", setting name = "a"
//   skipelem("a", name) = "", setting name = "a"
//   skipelem("", name) = skipelem("////", name) = 0
//
static const char *skipelem(const char *path, char *name)
{
        const char *s;
        int len;

        while (*path == '/')
                path++;
        if (*path == 0)
                return 0;
        s = path;
        while (*path != '/' && *path != 0)
                path++;
        len = path - s;
        if (len >= DIRSIZ)
                memmove(name, s, DIRSIZ);
        else {
                memmove(name, s, len);
                name[len] = 0;
        }
        while (*path == '/')
                path++;
        return path;
}

static struct inode* dirlookup(struct inode *dp, char *name)
{
        char sname[DIRSIZ];
        size_t n;
        usymlink_t obj;

        if (!S_ISDIR(dp->mode))
                panic("dirlookup not DIR");

        if (namecmp(name, ".") == 0 ) {
                return dp;
        }

        for (n = 0; n < CONTAINER_NR_PAGES; n++) {
                if (container_get_slot(dp->inum, n, &obj) != 0)
                        continue;
                if (page_get_name(obj, sname) != 0)
                        continue;
                if (namecmp(name, sname) == 0) {
                        return iget(obj);
                }
        }
        return NULL;
}

static struct inode* namex(const char *path, int nameiparent, char *name)
{
        struct inode *next, *ip;

        if (*path == '/') {
                ip = iget(fs_get_root_container());
        } else {
                ip = iget(current_working_directory());
        }

        while ((path = skipelem(path, name)) != 0) {
                if (!(S_ISDIR(ip->mode))) {
                        iput(ip);
                        return NULL;
                }
                if (nameiparent && *path == '\0') {
                        return ip;
                }

                next = dirlookup(ip, name);
                if (next != ip)
                        iput(ip);
                if (next == NULL)
                        return NULL;
                ip = next;
        }

        if (nameiparent) {
                iput(ip);
                return NULL;
        }

        return ip;
}

static struct inode* namei(const char *path)
{
        char name[DIRSIZ];
        return namex(path, 0, name);
}

static struct inode* nameiparent(const char *path, char *name)
{
        return namex(path, 1, name);
}

static struct inode* create(const char *path, mode_t mode)
{
        char name[DIRSIZ];
        struct dinode di;
        struct inode *ip, *dp;

        dp = nameiparent(path, name);
        if (dp == NULL)
                return NULL;

        ip = dirlookup(dp, name);
        if (ip != NULL) {
                iput(dp);
                if (ip != dp)
                        iput(ip);
                return NULL;
        }

        struct label secrecy, integrity, ownership;
        self_get_label(&secrecy, &integrity, &ownership);

        usymlink_t obj;

        // Creating process donates a small amount of page quota from its internal container
        usymlink_t quota_parent = self_get_internal_container(); /* dp->inum */

        if (S_ISDIR(mode)) {
                ASSERT_MSG(alloc_container(&obj, dp->inum, &secrecy, &integrity, name) == 0, "alloc_container");
                ASSERT_MSG(container_move_quota(quota_parent, obj, 128) == 0, "sys_container_move_quota");
        } else if (S_ISREG(mode)) {
                ASSERT_MSG(alloc_directory_pmd(&obj, dp->inum, &secrecy, &integrity, name) == 0, "alloc_directory_pmd");
        } else {
                panic("Can't create file with mode %u\n", mode);
        }

        di.fsize = 0;
        di.mode = mode;
        /* TODO: time stamps  */
        di.atime = 0;
        di.mtime = 0;
        di.ctime = 0;
        put_dinode(obj, &di);

        dp->fsize += PAGE_NAME_LEN;

        iput(dp);

        return iget(obj);
}

static long stdio_write(enum io_op op, struct iobuf *io)
{
        ASSERT_MSG(op == IO_OP_WRITE, "can not read stdio_write");
        ASSERT_MSG(io->len <= sizeof(io->buf), "invalid iobuf");
        char buf[PAGE_SIZE];
        memcpy(buf, io->buf, io->len);
        buf[io->len] = 0;
        sys_debug_print(buf);
        return io->len;
}

static long stdio_read(enum io_op op, struct iobuf *io)
{
        ASSERT_MSG(op == IO_OP_READ, "can not write stdio_read");
        ASSERT_MSG(io->len <= sizeof(io->buf), "invalid iobuf");
        size_t n = 0;
        char c;
        while (n < io->len) {
                while ((c = sys_debug_getchar()) == -EAGAIN);
                io->buf[n++] = c;
        }
        return n;
}

static long stdio(dev_t dev, struct iobuf *io)
{
        switch (io->op) {
        default:
                ASSERT_MSG(false, "Unsupported op");
        case IO_OP_READ:
                return stdio_read(io->op, io);
        case IO_OP_WRITE:
                return stdio_write(io->op, io);
        }
}

static long dev_null(dev_t dev, struct iobuf *io)
{
        switch (io->op) {
        default:
                ASSERT_MSG(false, "Unsupported op");
        case IO_OP_READ:
                return 0;
        case IO_OP_WRITE:
                return io->len;
        }
}

static long dev_zero(dev_t dev, struct iobuf *io)
{
        switch (io->op) {
        default:
                ASSERT_MSG(false, "Unsupported op");
        case IO_OP_READ:
                memset(io->buf, 0, io->len);
                return io->len;
        case IO_OP_WRITE:
                return io->len;
        }
}

static void _init_file_table()
{
        long r;

        static_assert(sizeof(struct file) * NFILES < FS_FILE_STRUCT_SIZE, "file table too large");
        static_assert(sizeof(struct inode) * NFILES < FS_FILE_INODE_SIZE, "inode table too large");

        /*  Map segment for file and inode tables */
        r = map_pages(FS_FILE_STRUCT_START, FS_FILE_STRUCT_SIZE,
                      PTE_PRESENT | PTE_USER | PTE_PSE | PTE_RW);
        ASSERT_MSG(r == 0, "map_pages");
//        r = map_pages(FS_FILE_INODE_START, FS_FILE_INODE_SIZE,
//                      PTE_PRESENT | PTE_USER | PTE_PSE | PTE_RW);
        ASSERT_MSG(r == 0, "map_pages");

        memset(file_table, 0, sizeof(struct file) * NFILES);
        memset(inodes, 0, sizeof(struct inode) * NFILES);
}

static void _init_stdio(void)
{
        struct dinode di;
        usymlink_t dev;
        struct label secrecy;
        struct label integrity;
        struct label ownership;
        struct label guard;
        label_init(&secrecy);
        label_init(&integrity);
        label_init(&ownership);
        label_init(&guard);
        di.fsize = 0;
        di.mode = S_IFCHR;
        di.atime = 0;
        di.mtime = 0;
        di.ctime = 0;

        struct inode *ip = create("/dev/", S_IFDIR);

        long r;

        // /dev/tty
        r = alloc_call_gate(&dev, ip->inum, &secrecy, &integrity,
                        &ownership, &guard, self_get_pud(), stdio, 0, "tty");
        ASSERT_MSG(r == 0, "alloc_call_gate: tty");
        put_dinode(dev, &di);
        ip->fsize += PAGE_NAME_LEN;

        // /dev/null
        r = alloc_call_gate(&dev, ip->inum, &secrecy, &integrity,
                        &ownership, &guard, self_get_pud(), dev_null, 0, "null");
        ASSERT_MSG(r == 0, "alloc_call_gate: null");
        put_dinode(dev, &di);
        ip->fsize += PAGE_NAME_LEN;

        // /dev/zero
        r = alloc_call_gate(&dev, ip->inum, &secrecy, &integrity,
                        &ownership, &guard, self_get_pud(), dev_zero, 0, "zero");
        ASSERT_MSG(r == 0, "alloc_call_gate: zero");
        put_dinode(dev, &di);
        ip->fsize += PAGE_NAME_LEN;

        iput(ip);
}

void _init_fs(void)
{
        struct dinode di;
        di.fsize = 0;
        di.mode = S_IFDIR;
        di.atime = 0;
        di.mtime = 0;
        di.ctime = 0;
        put_dinode(fs_get_root_container(), &di);
        _init_file_table();
        _init_stdio();
}


/* syscall interface */

long hs_mknod(const char *path, mode_t mode, dev_t dev)
{
        struct inode *ip;
        ASSERT_MSG(S_ISREG(mode) || S_ISDIR(mode), "TBD", path);
        ip = create(path, mode);
        if (ip == NULL)
                return -EEXIST;
        iput(ip);
        return 0;
}

long hs_open(const char *pathname, int flags, ...)
{
        int r = -ENOENT;
        struct inode *ip;
        int fd;

        if (strlen(pathname) == 0)
                return -ENOENT;

        if (flags & O_CREAT) {
                ASSERT_MSG((flags & O_DIRECTORY) == 0, "Can not O_CREAT directory");
                r = hs_mknod(pathname, S_IFREG, 0);
        }

        ip = namei(pathname);
        if (ip == NULL) {
                return r;
        }

        if ((fd = find_free_fd(0)) < 0)
                return fd;

        file_table[fd].ino = ip;
        file_table[fd].offset = 0;
        file_table[fd].flags = flags;
        file_table[fd].size = file_size(ip->inum);

        if (flags & O_DIRECTORY || S_ISDIR(ip->mode)) {
                ASSERT_MSG((flags & O_RDONLY) == 0, "Can only open directory read only");
                ASSERT_MSG(S_ISDIR(ip->mode), "");
        } else if (S_ISREG(ip->mode)) {
                map_file(fd);
        }

        return fd;
}

long hs_close(int fd)
{
        if (!fd_is_open(fd))
                return -EBADF;
        struct file *f = &file_table[fd];
        usymlink_t pud = USYMLINK_INVALID;
        pud = self_get_pud();
        if (S_ISREG(f->ino->mode))
                directory_unlink_pmd(pud, pdpt_index((uintptr_t)f->base));
        iput(f->ino);
        f->ino = NULL;
        f->base = 0;
        f->offset = 0;
        return 0;
}

long hs_fstat(int fd, struct stat *st)
{
        ASSERT_MSG(fd_is_open(fd),
                        "fd %d is not associated with an open file or directory", fd);
        struct file *f = &file_table[fd];
        st->st_mode = f->ino->mode;
        st->st_dev = 0;
        st->st_ino = 0; /* TODO */
        st->st_nlink = 0;
        st->st_size = f->ino->fsize;
        st->st_atime = f->ino->atime;
        st->st_mtime = f->ino->mtime;
        st->st_ctime = f->ino->ctime;
        return 0;
}

off_t hs_lseek(int fd, off_t offset, int whence)
{
        struct file *f;

        ASSERT_MSG(fd_is_open(fd), "fd %d is not associated with an open file or directory", fd);

        f = &file_table[fd];

        switch (whence) {
        default:
                ASSERT_MSG(false, "TBD: %d", whence);
        case SEEK_SET:
                f->offset = offset;
                break;
        case SEEK_CUR:
                f->offset += offset;
                break;
        case SEEK_END:
                f->offset = (off_t)f->ino->fsize + offset;
                break;
        }

        ASSERT_MSG(f->offset >= 0, "invalid offset");

        return f->offset;
}

ssize_t hs_pread(int fd, void *buf, size_t nbytes, off_t offset)
{
        ASSERT_MSG(fd_is_readable(fd), "fd %d is not open for reading", fd);
        struct file *f = &file_table[fd];
        if (S_ISREG(f->ino->mode)) {
                if (f->ino->fsize <= offset)
                        return 0;
                uint64_t rem = f->ino->fsize - offset;
                uint64_t readsz = nbytes < rem ? nbytes : rem;
                memcpy(buf, f->base + offset, readsz);
                return readsz;
        } else if (S_ISCHR(f->ino->mode)) {
                // fsize for chr device?
                long r;
                struct iobuf iobuf = { .op = IO_OP_READ };
                size_t len = nbytes < sizeof(iobuf.buf) ? nbytes : sizeof(iobuf.buf);
                memcpy(iobuf.buf, buf, len);
                iobuf.len = len;
                iobuf.offset = offset;
                r = gate_call(f->ino->inum, self_get_internal_container(), (uintptr_t)(void*)&iobuf);
                if (r > 0)
                        memcpy(buf, iobuf.buf, r);
                return r;
        }

        panic("hs_pread: unsupported mode %d in fd %d", f->ino->mode, fd);
}

ssize_t hs_read(int fd, void *buf, size_t nbytes)
{
        ASSERT_MSG(fd_is_open(fd), "fd %d is not associated with an open file", fd);
        ssize_t r;
        struct file *f = &file_table[fd];
        if ((r = hs_pread(fd, buf, nbytes, f->offset)) < 0)
                return r;
        f->offset += r;
        return r;
}

ssize_t hs_pwrite(int fd, const void *buf, size_t nbytes, off_t offset)
{
        ASSERT_MSG(fd_is_writable(fd), "fd %d is not open for writing", fd);
        struct file *f = &file_table[fd];
        if (S_ISREG(f->ino->mode)) {
                // map a new block at f->ino->inum
                while (offset + nbytes >= f->size) {
                        long r;
                        usymlink_t blk, directory;
                        struct label secrecy, integrity, ownership;
                        self_get_label(&secrecy, &integrity, &ownership);
                        page_get_container(f->ino->inum, &directory);

                        // move quota from the internal container to the directory of this file.
                        r = container_move_quota(self_get_internal_container(), directory, 3);
                        ASSERT_MSG(r == 0, "sys_container_move_quota");
                        r = container_move_uquota(self_get_internal_container(), directory, 1);
                        ASSERT_MSG(r == 0, "sys_container_move_uquota");

                        // allocate a block in the current directory
                        alloc_block(&blk, directory, &secrecy, &integrity, NULL);

                        directory_link_block(f->ino->inum, pmd_index((uintptr_t)f->base + f->size), blk, PTE_PRESENT | PTE_USER | PTE_RW | PTE_PSE);

                        f->size += SZ_2M;
                }
                ASSERT_MSG(offset + nbytes < f->size, "hs_pwrite: writing out of bounds");
                memcpy(f->base + offset, buf, nbytes);
                f->ino->fsize = max(f->ino->fsize, offset + nbytes);
                return nbytes;
        } else if (S_ISCHR(f->ino->mode)) {
                struct iobuf iobuf = { .op = IO_OP_WRITE };
                size_t len = nbytes < sizeof(iobuf.buf) ? nbytes : sizeof(iobuf.buf) - 1;
                memcpy(iobuf.buf, buf, len);
                iobuf.len = len;
                iobuf.offset = offset;
                return gate_call(f->ino->inum, self_get_internal_container(), (uintptr_t)(void*)&iobuf);
        }
        panic("hs_pwrite: unsupported mode %d in fd %d", f->ino->mode, fd);
}

ssize_t hs_write(int fd, const void *buf, size_t nbytes)
{
        ASSERT_MSG(fd_is_open(fd), "fd %d is not associated with an open file", fd);
        ssize_t r;
        struct file *f = &file_table[fd];
        if ((r = hs_pwrite(fd, buf, nbytes, f->offset)) < 0)
                return r;
        f->offset += r;
        return r;
}

ssize_t hs_getent(int fd, struct nistar_dirent *dirp, unsigned int count)
{
        ASSERT_MSG(fd_is_mode(fd, S_IFDIR), "fd %d is not associated with an open directory", fd);
        struct file *f = &file_table[fd];
        size_t n;
        usymlink_t usym;
        for (n = 0; n * sizeof(struct nistar_dirent) < count && f->offset < CONTAINER_NR_PAGES; f->offset++) {
                if (container_get_slot(f->ino->inum, f->offset, &usym) != 0)
                        continue;
                if (page_get_name(usym, dirp->name) != 0)
                        continue;
                if (*dirp->name == 0)
                        continue;
                dirp->slot = f->offset;
                n++;
                dirp++;
        }
        if (n == 0) {
                ASSERT_MSG(f->offset >= CONTAINER_NR_PAGES, "getent");
                return -ENOENT;
        }
        return n * sizeof(struct nistar_dirent);
}

long hs_mkdir(const char *path, mode_t mode)
{
        struct inode *ip;
        ip = create(path, S_IFDIR | mode);
        if (ip == NULL)
                return -EEXIST;
        iput(ip);
        return 0;
}

long hs_mkdir_p(const char *path, mode_t mode)
{
        long r = -EINVAL;
        char dirp[DIRSIZ * 128];
        char name[DIRSIZ];
        dirp[0] = 0;
        while ((path = skipelem(path, name)) != 0) {
                strlcat(dirp, name, sizeof(dirp));
                r = hs_mkdir(dirp, mode);
                strlcat(dirp, "/", sizeof(dirp));
        }

        return r;
}

long hs_unlink(const char *pathname)
{
        /* FIXME */
        return -ENOSYS;
}

long hs_dup2(int old, int new)
{
        ASSERT_MSG(fd_is_open(old), "fd %d is not associated with an open file or directory", old);
        if (!fd_is_valid(old))
                return -EBADF;

        if (old == new)
                return 0;

        if (fd_is_open(new))
                hs_close(new);

        struct file *oldf = &file_table[old];
        struct file *newf = &file_table[new];
        memcpy(newf, oldf, sizeof(struct file));

        incref(newf->ino);

        return 0;
}

long hs_dup(int fd)
{
        int r;
        int newfd;
        ASSERT_MSG(fd_is_open(fd), "fd %d is not associated with an open file or directory", fd);
        if ((newfd = find_free_fd(0)) < 0)
                return newfd;
        r = hs_dup2(fd, newfd);
        ASSERT_MSG(r == 0, "hs_dup2");
        if (r < 0)
                return r;
        return newfd;
}

long hs_pipe2(int pipefd[2], int flags)
{
        debug_printf("FIXME: hs_pipe2\n");
        return -ENOSYS;
}

long hs_fsync(int fd)
{
        ASSERT_MSG(fd_is_open(fd), "fd %d is not associated with an open file or directory", fd);
        struct file *f = &file_table[fd];
        isync(f->ino);
        return 0;
}

usymlink_t current_working_directory()
{
        static usymlink_t cwd = USYMLINK_INVALID;
        if (!usymlink_is_valid(cwd)) {
                cwd = fs_get_root_container();
        }
        return cwd;
}

long hs_opengate(usymlink_t gate, int flags)
{
        struct file *f;
        struct inode *ip;

        int fd = find_free_fd(0);
        ASSERT_MSG(fd_is_valid(fd), "Invalid fd");
        ASSERT_MSG(!fd_is_open(fd), "FD not free");

        f = &file_table[fd];

        ip = iget(gate);
        ASSERT_MSG(ip != NULL, "iget");

        ip->mode = S_IFCHR;

        file_table[fd].ino = ip;
        file_table[fd].offset = 0;
        file_table[fd].flags = flags;
        file_table[fd].size = 0;

        return fd;
}
