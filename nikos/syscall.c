#include <asm/desc.h>
#include <asm/processor.h>
#include <asm/setup.h>
#include <sys/errno.h>
#include <sys/string.h>
#include "elf.h"
#include "param.h"
#include "proc.h"
#include "vm.h"

enum {
#define __SYSCALL(x) SYS_##x,
#include <uapi/mcertikos/syscall.inc>
#undef __SYSCALL
};

static long sys_nop(void)
{
        return -ENOSYS;
}

static long sys_get_quota(void)
{
        return get_current_proc()->nr_free_pages;
}

static long sys_spawn(uint64_t fileid, uint64_t quota)
{
        struct proc *proc = get_current_proc();
        uint64_t pid;

        if (fileid >= NR_ELF_FILES)
                return -EINVAL;
        if (proc->nr_free_pages < quota)
                return -EINVAL;
        if (proc->nr_children >= NR_CHILDREN)
                return -ENOMEM;

        pid = current_pid * NR_CHILDREN + proc->nr_children + 1;
        if (pid >= NR_PROCS)
                return -ENOMEM;

        proc->nr_free_pages -= quota;
        ++proc->nr_children;

        proc_new(pid, fileid, quota);
        /* will load elf later */

        return pid;
}

static long sys_yield(void)
{
        struct proc *proc = get_current_proc();
        uint64_t next = proc->next;

#if 0
        pr_info("yield: %zu -> %zu\n", current_pid, next);
#endif

        /* save registers */
        memcpy(&proc->cpu, get_current_pt_regs(), sizeof(proc->cpu));

        if (get_proc(next)->state == PROC_STATE_RUN)
                vm_switch(next);

        return -EINVAL;
}

static long sys_print(uint8_t c)
{
        printk(-1, "%c", c);
        return 0;
}

void *syscall_table[NR_syscalls] = {
        [0 ... NR_syscalls - 1] = sys_nop,
#define __SYSCALL(x) [SYS_##x] = sys_##x,
#include <uapi/mcertikos/syscall.inc>
#undef __SYSCALL
};

static long handle_page_fault(uint64_t slot)
{
        long pid = current_pid, r;

        r = vm_alloc(pid, slot);
        /* not necessary */
        if (r < 0)
            return r;
        /* load elf on demand */
        if (slot == ELF_VA_SLOT) {
                size_t fileid = get_proc(pid)->fileid;
                memcpy(vm_get_data(r), elf_get_data(fileid), SZ_2M);
        }
        return 0;
}

void do_page_fault(struct pt_regs *regs, long error_code)
{
        uintptr_t va = read_cr2();
        size_t slot = va / SZ_2M;
        long r;

        /* must be user page fault */
        BUG_ON(!(regs->cs & 3));
#if 0
        pr_info("page fault: pid=%lu va=0x%lx rip=0x%lx\n", pid, va, get_proc(pid)->cpu.rip);
#endif

        r = handle_page_fault(slot);

        if (r < 0)
                sys_yield();
}

