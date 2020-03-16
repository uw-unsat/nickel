#include <asm/msr.h>
#include <asm/processor.h>
#include <asm/ptrace.h>

void show_regs(struct pt_regs *regs)
{
        unsigned long cr0 = 0L, cr2 = 0L, cr3 = 0L, cr4 = 0L, fs, gs, shadowgs;
        unsigned int fsindex, gsindex;
        unsigned int ds, cs, es;

        printk(LOGLEVEL_DEFAULT, "RIP: %04lx:%pS\n",
               regs->cs & 0xffff, (void *)regs->rip);
        printk(LOGLEVEL_DEFAULT, "RSP: %04lx:%016lx RFLAGS: %08lx",
               regs->ss, regs->rsp, regs->rflags);
        if (regs->orig_rax != -1)
                pr_cont(" ORIG_RAX: %016lx\n", regs->orig_rax);
        else
                pr_cont("\n");

        printk(LOGLEVEL_DEFAULT, "RAX: %016lx RBX: %016lx RCX: %016lx\n",
               regs->rax, regs->rbx, regs->rcx);
        printk(LOGLEVEL_DEFAULT, "RDX: %016lx RSI: %016lx RDI: %016lx\n",
               regs->rdx, regs->rsi, regs->rdi);
        printk(LOGLEVEL_DEFAULT, "RBP: %016lx R08: %016lx R09: %016lx\n",
               regs->rbp, regs->r8, regs->r9);
        printk(LOGLEVEL_DEFAULT, "R10: %016lx R11: %016lx R12: %016lx\n",
               regs->r10, regs->r11, regs->r12);
        printk(LOGLEVEL_DEFAULT, "R13: %016lx R14: %016lx R15: %016lx\n",
               regs->r13, regs->r14, regs->r15);

        asm("movl %%ds,%0" : "=r" (ds));
        asm("movl %%cs,%0" : "=r" (cs));
        asm("movl %%es,%0" : "=r" (es));
        asm("movl %%fs,%0" : "=r" (fsindex));
        asm("movl %%gs,%0" : "=r" (gsindex));

        fs = rdmsrl(MSR_FS_BASE);
        gs = rdmsrl(MSR_GS_BASE);
        shadowgs = rdmsrl(MSR_KERNEL_GS_BASE);

        cr0 = read_cr0();
        cr2 = read_cr2();
        cr3 = read_cr3();
        cr4 = read_cr4();

        printk(LOGLEVEL_DEFAULT, "FS:  %016lx(%04x) GS:%016lx(%04x) knlGS:%016lx\n",
               fs, fsindex, gs, gsindex, shadowgs);
        printk(LOGLEVEL_DEFAULT, "CS:  %04x DS: %04x ES: %04x CR0: %016lx\n",
               cs, ds, es, cr0);
        printk(LOGLEVEL_DEFAULT, "CR2: %016lx CR3: %016lx CR4: %016lx\n",
               cr2, cr3, cr4);

        show_stack(regs);
}

void show_stack(struct pt_regs *regs)
{
        int cpu = smp_processor_id();
        unsigned long *stack_start, *stack_end;
        unsigned long *bp;

        printk(LOGLEVEL_DEFAULT, "Call Trace:\n");

        stack_start = (void *)cpu_stacks[cpu];
        stack_end = (void *)stack_start + CPU_STACK_SIZE;

        bp = regs ? (unsigned long *)regs->rbp : __builtin_frame_address(0);

        while (bp >= stack_start && bp < stack_end) {
                unsigned long addr = *(bp + 1);

                printk(LOGLEVEL_DEFAULT, "%pB\n", (void *)addr);
                bp = (unsigned long *)*bp;
        }
}

void dump_stack(void)
{
        show_stack(NULL);
}
