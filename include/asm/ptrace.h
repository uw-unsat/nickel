#pragma once

struct pt_regs {
/*
 * C ABI says these regs are callee-preserved. They aren't saved on kernel entry
 * unless syscall needs a complete, fully filled "struct pt_regs".
 */
        unsigned long r15;
        unsigned long r14;
        unsigned long r13;
        unsigned long r12;
        unsigned long rbp;
        unsigned long rbx;
/* These regs are callee-clobbered. Always saved on kernel entry. */
        unsigned long r11;
        unsigned long r10;
        unsigned long r9;
        unsigned long r8;
        unsigned long rax;
        unsigned long rcx;
        unsigned long rdx;
        unsigned long rsi;
        unsigned long rdi;
/*
 * On syscall entry, this is syscall#. On CPU exception, this is error code.
 * On hw interrupt, it's IRQ number:
 */
        unsigned long orig_rax;
/* Return frame for iretq */
        unsigned long rip;
        unsigned long cs;
        unsigned long rflags;
        unsigned long rsp;
        unsigned long ss;
/* top of stack page */
};

/*
 * user_mode(regs) determines whether a register set came from user mode.
 */
static inline int user_mode(struct pt_regs *regs)
{
        return !!(regs->cs & 3);
}

void show_regs(struct pt_regs *regs);
void show_stack(struct pt_regs *regs);
