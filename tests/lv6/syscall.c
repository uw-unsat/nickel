#include <asm/setup.h>
#include <sys/errno.h>

static long cls;

static long sys_nop(void)
{
        return -ENOSYS;
}

static long sys_hey(long x)
{
        cls = x;
        pr_info("hey %ld, va=0x%p\n", x, &cls);
        return 0;
}

static long sys_bye(void)
{
        pr_info("bye %ld\n", cls);
        die();
        return 0;
}

void *syscall_table[NR_syscalls] = {
        [0 ... NR_syscalls - 1] = &sys_nop,
        [0] = sys_hey,
        [1] = sys_bye,
};
