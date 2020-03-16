#include <asm/ioctls.h>
#include <assert.h>
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <nistar/env.h>
#include <nistar/exec.h>
#include <nistar/fork.h>
#include <nistar/libfs.h>
#include <nistar/memlayout.h>
#include <nistar/ulib.h>
#include <io/sizes.h>
#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/syscall.h>
#include <sys/uio.h>
#include <termios.h>

#define ARRAY_SIZE(arr) (sizeof(arr) / sizeof((arr)[0]))

static long sys_ignore(void)
{
        return 0;
}

static noreturn void sys_exit_group(int status)
{
        hs_exit(status);
}

static long sys_ioctl(int fd, unsigned int request, void *arg)
{
        switch (request) {
        case TIOCGWINSZ:
        case TCGETS:
        case TCSETS + TCSANOW:
        case TCSETS + TCSAFLUSH:
                return 0;
        }
        ASSERT_MSG(false, "ioctl request not supported\n");
        return -EINVAL;
}

static long sys_fcntl(int filedes, int cmd, ...)
{
        switch (cmd) {
        default:
                break;
        case F_SETFD:
        case F_SETFL:
        case F_SETLK:
                // TODO...
                return 0;
        case F_GETFL:
                return 0;
        }
        ASSERT_MSG(false, "fcntl request %d not supported\n", cmd);
        return -EINVAL;
}

static long sys_mmap(void *addr, size_t len, int prot, int flags, int fildes, off_t off)
{
        pteval_t perm;
        size_t i, j;

        /* validate arguments */

        // If len is zero, mmap() shall fail
        if (len == 0) {
                return -EINVAL;
        }
        // value of flags is the bitwise-inclusive OR of these options,
        if (flags & ~(MAP_SHARED | MAP_PRIVATE | MAP_FIXED | MAP_ANONYMOUS)) {
                return -EINVAL;
        }
        // either MAP_SHARED or MAP_PRIVATE can be specified, but not both.
        if ((flags & MAP_PRIVATE) && (flags & MAP_SHARED)) {
                return -EINVAL;
        }
        if ((flags & MAP_FIXED)) {
                return -ENOTSUP;
        }
        // prot shall be either PROT_NONE or ...
        if (prot & PROT_NONE && prot != PROT_NONE) {
                return -EINVAL;
        }
        // the bitwise-inclusive OR of one or more of the following:
        // PROT_READ, PROT_WRITE, PROT_EXEC
        if (prot & ~(PROT_READ | PROT_WRITE | PROT_EXEC)) {
                return -EINVAL;
        }

        /* unsupported */

        if (addr == 0) {
                usymlink_t pmd;
                page_walk(MMAP_START, &pmd);

                usymlink_t xx;
                // find contiguous len / SZ_2M many blocks available in the pmd
                size_t requested = roundup(len, SZ_2M) / SZ_2M;
                for (i = 0; i < DIRECTORY_NR_ENTRIES; i++) {
                        for (j = 0; j < requested; j++) {
                                if (directory_get_slot(pmd, i + j, &xx) == 0) {
                                        //  slot j is not free
                                        i += j;
                                        break;
                                }
                        }
                        if (j == requested) {
                                // found enough contigous blocks
                                addr = (void*)MMAP_START + (SZ_2M * i);
                                break;
                        }
                }
        }

        ASSERT_MSG(addr != 0, "mmap");
        ASSERT_MSG((prot & PROT_NONE) == 0, "mmap");
        // Doesn't support shared mappings yet.
        // Should be easy enough to support. Allocate in a public container
        // with an empty label set.
        ASSERT_MSG((flags & MAP_SHARED) == 0, "mmap");
        // Don't support MAP_FIXED
        ASSERT_MSG((flags & MAP_FIXED) == 0, "mmap");

        ASSERT_MSG(fildes < 0, "mmap");
        ASSERT_MSG(off == 0, "mmap");

        perm = PTE_PRESENT | PTE_USER | PTE_PSE;

        if (flags & PROT_WRITE)
                perm |= PTE_RW;
        if ((flags & PROT_EXEC) == 0)
                perm |= PTE_NX;

        map_pages((uintptr_t)addr, len, perm);

        return (long)addr;
}

static long sys_munmap(void *addr, size_t len)
{
        long r;
        r = unmap_pages((uintptr_t)addr, len);
        ASSERT_MSG(r == 0, "sys_munmap");
        return r;
}

static ssize_t sys_writev(int fd, const struct iovec *iov, int iovcnt)
{
        ssize_t i, total = 0;

        for (i = 0; i < iovcnt; i++) {
                ssize_t n = 0;

                while (n < iov[i].iov_len) {
                        ssize_t c;

                        c = hs_write(fd, iov[i].iov_base + n, iov[i].iov_len - n);
                        if (c < 0)
                                return total > 0 ? total : c;

                        total += c;
                        n += c;
                }
        }

        return total;
}

static ssize_t sys_readv(int fd, const struct iovec *iov, int iovcnt)
{
        ssize_t i, total = 0;

        for (i = 0; i < iovcnt; i++) {
                size_t n = 0;

                while (n < iov[i].iov_len) {
                        ssize_t c;

                        c = hs_read(fd, iov[i].iov_base + n, iov[i].iov_len - n);
                        if (c <= 0)
                                return total > 0 ? total : c;

                        total += c;
                        n += c;
                }
        }

        return total;
}

static long sys_getdents64(int fd, struct dirent *dirp, unsigned int count)
{
        struct nistar_dirent di;
        size_t n = 0;
        ssize_t len = 0;
        for (n = 0; n * sizeof(struct dirent) < count; n++) {
                len = hs_getent(fd, &di, sizeof(di));
                if (len < 0) {
                        ASSERT_MSG(len == -ENOENT, "getent");
                        if (n == 0)
                                return len;
                        break;
                }
                ASSERT_MSG(len == sizeof(struct nistar_dirent), "getent");
                strlcpy(dirp->d_name, di.name, sizeof(dirp->d_name));
                dirp->d_reclen = sizeof(struct dirent);
                dirp->d_off = di.slot;
                dirp++;
        }
        return n * sizeof(struct dirent);
}

/* FIXME: lstat doesn't follow symlinks */
static long sys_lstat(const char *path, struct stat *buf)
{
        int r, fd;
        fd = hs_open(path, O_RDONLY);
        if (fd < 0)
                return fd;
        r = hs_fstat(fd, buf);
        hs_close(fd);
        return r;
}

static long sys_stat(const char *path, struct stat *buf)
{
        return sys_lstat(path, buf);
}

static int sys_access(const char *pathname, mode_t mode)
{
        struct stat statbuf;
        int r;

        r = sys_stat(pathname, &statbuf);
        /* TODO: check mode? */
        return r;
}

static long sys_rt_sigprocmask(int how, const sigset_t *set, sigset_t *oldset, size_t sigsetsize)
{
        // debug_printf("FIXME: sys_rt_sigprocmask\n");
        return 0;
}

static long sys_rt_sigaction(int signum, const struct sigaction *act, struct sigaction *oldact)
{
        // debug_printf("FIXME: sys_rt_sigaction\n");
        return 0;
}

static pid_t sys_getpid(void)
{
        // debug_printf("FIXME: getpid\n");
        return -ENOSYS;
}

static int sys_clock_gettime(clockid_t clk_id, struct timespec *tp)
{
        uint64_t msec;

        msec = sys_debug_uptime();
        tp->tv_sec = msec / 1000000;
        tp->tv_nsec = (msec % 1000000) * 1000;
        return 0;
}

static pid_t sys_fork()
{
        long r;
        usymlink_t pid;
        r = hs_fork(&pid);
        ASSERT_MSG(r == 0, "fork");
        if (!usymlink_is_valid(pid))
                return 0;
        // TODO: What to return? For now just return some random bits
        return (pid_t)(pid.upage);
}

static pid_t sys_gettid()
{
        // debug_printf("FIXME: gettid\n");
        return 1;
}

static pid_t sys_wait4(pid_t pid, int *wstatus, int options, struct rusage *rusage)
{
        long r;
        usymlink_t child;
        ASSERT_MSG(pid == -1, "Waiting on a specific pid not supported");
        // TODO: mapping from pid to usym
        r = hs_wait4(USYMLINK_INVALID, wstatus, options, rusage, &child);
        ASSERT_MSG(r == 0, "hs_wait4: %ld", r);
        if (r < 0)
                return r;
        return (pid_t)(child.upage);
}

static char* sys_getcwd(char *buf, size_t size)
{
        debug_printf("FIXME: cwd\n");
        strlcpy(buf, "/", size);
        return buf;
}

static uid_t sys_geteuid(void)
{
        debug_printf("FIXME: geteuid\n");
        return -ENOSYS;
}

static long sys_chown(const char *pathname, uid_t owner, gid_t group)
{
        debug_printf("FIXME: chown\n");
        return 0;
}

static long sys_fchown(int fildes, uid_t owner, gid_t group)
{
        debug_printf("FIXME: fchown\n");
        return 0;
}

static long sys_pipe(int pipefd[2])
{
        return hs_pipe2(pipefd, 0);
}

static __always_inline uint64_t rdtsc(void)
{
        uint64_t low, high;
        asm volatile("rdtsc" : "=a" (low), "=d" (high));
        return low | (high << 32);
}

static long sys_nanosleep(const struct timespec *rqtp, struct timespec *rmtp)
{
        time_t selapsed = 0;
        uint64_t nelapsed = 0;

        uint64_t last, now;
        now = last = rdtsc();

        while (1) {
                if (selapsed > rqtp->tv_sec && nelapsed > rqtp->tv_nsec) {
                        return 0;
                }

                now = rdtsc();
                nelapsed += now - last;
                selapsed += nelapsed / 1000000000;
                nelapsed = nelapsed % 1000000000;
                last = now;
        }
        return -1;
}

static void *linux_syscalls[] = {
        [__NR_mmap]             = sys_mmap,
        [__NR_munmap]           = sys_munmap,
        [__NR_madvise]          = sys_ignore,
        [__NR_brk]              = hs_brk,
        [__NR_ioctl]            = sys_ioctl,
        [__NR_exit]             = hs_exit,
        [__NR_exit_group]       = sys_exit_group,
        [__NR_pwrite64]         = hs_pwrite,
        [__NR_write]            = hs_write,
        [__NR_writev]           = sys_writev,
        [__NR_pread64]          = hs_pread,
        [__NR_read]             = hs_read,
        [__NR_readv]            = sys_readv,
        [__NR_getdents64]       = sys_getdents64,
        [__NR_fstat]            = hs_fstat,
        [__NR_lstat]            = sys_lstat,
        [__NR_stat]             = sys_stat,
        [__NR_access]           = sys_access,
        [__NR_rt_sigprocmask]   = sys_rt_sigprocmask,
        [__NR_rt_sigaction]     = sys_rt_sigaction,
        [__NR_umask]            = sys_ignore,
        [__NR_getpid]           = sys_getpid,
        [__NR_open]             = hs_open,
        [__NR_close]            = hs_close,
        [__NR_mknod]            = hs_mknod,
        [__NR_mkdir]            = hs_mkdir,
        [__NR_unlink]           = hs_unlink,
        [__NR_fcntl]            = sys_fcntl,
        [__NR_lseek]            = hs_lseek,
        [__NR_dup]              = hs_dup,
        [__NR_dup2]             = hs_dup2,
        [__NR_execve]           = hs_execve,
        [__NR_clock_gettime]    = sys_clock_gettime,
        [__NR_select]           = sys_ignore,
        [__NR_fork]             = sys_fork,
        [__NR_gettid]           = sys_gettid,
        [__NR_wait4]            = sys_wait4,
        [__NR_getcwd]           = sys_getcwd,
        [__NR_geteuid]          = sys_geteuid,
        [__NR_fsync]            = hs_fsync,
        [__NR_chown]            = sys_chown,
        [__NR_fchown]           = sys_fchown,
        [__NR_pipe]             = sys_pipe,
        [__NR_pipe2]            = hs_pipe2,
        [__NR_nanosleep]        = sys_nanosleep,
};

long __syscall(long nr, long arg0, long arg1, long arg2, long arg3, long arg4, long arg5)
{
        long (*f)(long, long, long, long, long, long) = NULL;

        if (nr < ARRAY_SIZE(linux_syscalls))
                f = linux_syscalls[nr];

        if (!f) {
                debug_printf("syscall %ld not implemented\n", nr);
                ASSERT_MSG(false, "");
                return -ENOSYS;
        }

        return f(arg0, arg1, arg2, arg3, arg4, arg5);
}
