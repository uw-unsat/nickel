// #include <fcntl.h>
#include <nistar/ulib.h>
#include <sys/stat.h>

#define NFILES 128

struct nistar_dirent {
        size_t slot;
        char name[32];
};

enum io_op {
        IO_OP_READ = 1,
        IO_OP_WRITE,
};

struct iobuf {
        enum io_op op;
        size_t len;
        off_t offset;
        char buf[PAGE_SIZE];
};

usymlink_t current_working_directory();
long hs_mknod(const char *path, mode_t mode, dev_t dev);
long hs_open(const char *pathname, int flags, ...);
long hs_close(int fd);
long hs_fstat(int fd, struct stat *st);
long hs_mkdir(const char *path, mode_t mode);
long hs_mkdir_p(const char *path, mode_t mode);
long hs_unlink(const char *pathname);
ssize_t hs_pread(int fd, void *buf, size_t nbytes, off_t offset);
ssize_t hs_read(int fd, void *buf, size_t nbytes);
ssize_t hs_pwrite(int fd, const void *buf, size_t nbytes, off_t offset);
ssize_t hs_getent(int fd, struct nistar_dirent *dirp, unsigned int count);
ssize_t hs_write(int fd, const void *buf, size_t nbytes);
off_t hs_lseek(int fd, off_t offset, int whence);
long hs_dup2(int old, int new);
long hs_dup(int fd);
long hs_pipe2(int pipefd[2], int flags);
long hs_fsync(int fd);
long hs_opengate(usymlink_t gate, int flags);
