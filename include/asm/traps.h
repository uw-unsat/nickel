#pragma once

#include <asm/ptrace.h>
#include <sys/types.h>

/* Interrupts/Exceptions */
enum {
        X86_TRAP_DE = 0,        /*  0, Divide-by-zero */
        X86_TRAP_DB,            /*  1, Debug */
        X86_TRAP_NMI,           /*  2, Non-maskable Interrupt */
        X86_TRAP_BP,            /*  3, Breakpoint */
        X86_TRAP_OF,            /*  4, Overflow */
        X86_TRAP_BR,            /*  5, Bound Range Exceeded */
        X86_TRAP_UD,            /*  6, Invalid Opcode */
        X86_TRAP_NM,            /*  7, Device Not Available */
        X86_TRAP_DF,            /*  8, Double Fault */
        X86_TRAP_OLD_MF,        /*  9, Coprocessor Segment Overrun */
        X86_TRAP_TS,            /* 10, Invalid TSS */
        X86_TRAP_NP,            /* 11, Segment Not Present */
        X86_TRAP_SS,            /* 12, Stack Segment Fault */
        X86_TRAP_GP,            /* 13, General Protection Fault */
        X86_TRAP_PF,            /* 14, Page Fault */
        X86_TRAP_SPURIOUS,      /* 15, Spurious Interrupt */
        X86_TRAP_MF,            /* 16, x87 Floating-Point Exception */
        X86_TRAP_AC,            /* 17, Alignment Check */
        X86_TRAP_MC,            /* 18, Machine Check */
        X86_TRAP_XF,            /* 19, SIMD Floating-Point Exception */
        X86_TRAP_IRET = 32,     /* 32, IRET Exception */
};

void divide_error(void);
void int3(void);
void overflow(void);
void bounds(void);
void invalid_op(void);
void device_not_available(void);
void double_fault(void);
void coprocessor_segment_overrun(void);
void invalid_TSS(void);
void segment_not_present(void);
void stack_segment(void);
void general_protection(void);
void page_fault(void);
void async_page_fault(void);
void spurious_interrupt_bug(void);
void coprocessor_error(void);
void alignment_check(void);
void machine_check(void);
void simd_coprocessor_error(void);

void apic_timer_interrupt(void);
void spurious_interrupt(void);
void error_interrupt(void);

noreturn void return_to_usermode(struct pt_regs *regs, phys_addr_t cr3);
