#include <asm/cache.h>
#include <asm/irq.h>
#include <asm/percpu.h>
#include <asm/segment.h>
#include <asm/setup.h>
#include <sys/errno.h>
#include <io/linkage.h>
#include "asm-offsets.h"
#include "calling.h"

/*
 * 64-bit SYSCALL instruction entry. Up to 6 arguments in registers.
 *
 * 64-bit SYSCALL saves rip to rcx, clears rflags.RF, then saves rflags to r11,
 * then loads new ss, cs, and rip from previously programmed MSRs.
 * rflags gets masked by a value from another MSR (so CLD and CLAC
 * are not needed). SYSCALL does not save anything on the stack
 * and does not change rsp.
 *
 * Registers on entry:
 * rax  system call number
 * rcx  return address
 * r11  saved rflags (note: r11 is callee-clobbered register in C ABI)
 * rdi  arg0
 * rsi  arg1
 * rdx  arg2
 * r10  arg3 (needs to be moved to rcx to conform to C ABI)
 * r8   arg4
 * r9   arg5
 * (note: r12-r15, rbp, rbx are callee-preserved in C ABI)
 *
 * Only called from user space.
 *
 * When user can change pt_regs->foo always force IRET. That is because
 * it deals with uncanonical addresses better. SYSRET has trouble
 * with them due to bugs in both AMD and Intel CPUs.
 */

.pushsection .entry_trampoline, "ax"

/*
 * The code here gets remapped into cpu_entry_area's trampoline.  This means
 * that the assembler and linker have the wrong idea as to where this code
 * lives (and, in fact, it's mapped more than once, so it's not even at a
 * fixed address).  So we can't reference any symbols outside the entry
 * trampoline and expect it to work.
 *
 * Instead, we carefully abuse %rip-relative addressing.
 * __entry_trampoline(%rip) refers to the start of the remapped entry
 * trampoline.  We can thus find cpu_entry_area with this macro:
 */

#define CPU_ENTRY_AREA          __entry_trampoline - CPU_ENTRY_AREA_entry_trampoline(%rip)
#define RSP_SCRATCH             CPU_ENTRY_AREA_entry_stack + SIZEOF_entry_stack - (SIZEOF_PTREGS - RSP) + CPU_ENTRY_AREA

ENTRY(do_syscall_64)
        swapgs

        /* save user %rsp */
        movq    %rsp, RSP_SCRATCH

        /* load the top of entry stack */
        movq    CPU_ENTRY_AREA_tss + TSS_sp0 + CPU_ENTRY_AREA, %rsp

        /* construct struct pt_regs on entry stack */
        pushq   $USER_DS                        /* pt_regs->ss */
        subq    $8, %rsp                        /* already in pt_regs->rsp */
        pushq   %r11                            /* pt_regs->rflags */
        pushq   $USER_CS                        /* pt_regs->cs */
        pushq   %rcx                            /* pt_regs->rip */
        pushq   %rax                            /* pt_regs->orig_rax */
        pushq   %rdi
        pushq   %rsi
        pushq   %rdx
        pushq   %rcx
        pushq   $-ENOSYS                        /* pt_regs->rax */
        pushq   %r8
        pushq   %r9
        pushq   %r10
        pushq   %r11
        pushq   %rbx
        pushq   %rbp
        pushq   %r12
        pushq   %r13
        pushq   %r14
        pushq   %r15

        cmpq    $NR_syscalls, %rax
        jae     .Ldo_syscall_64_return          /* return -ENOSYS (already in pt_regs->rax) */

        /* switch to kernel page table */
        SAVE_AND_SWITCH_TO_KERNEL_CR3 scratch_reg=%rsp save_reg=%r14

        /* switch to kernel stack (must occur before relocation) */
        movq    CPU_ENTRY_AREA_tss + TSS_sp1 + CPU_ENTRY_AREA, %rsp

        /* save offseted address for return (must occur before relocation) */
        leaq    .Ldo_syscall_64_after_call(%rip), %r12

        /* relocate to identity mapping (must occur after %cr3 switch) */
        RELOCATE_TO_KERNEL_RIP scratch_reg=%rcx

        movq    %r10, %rcx
        call    *syscall_table(, %rax, 8)

        /* relocate to offseted .Ldo_syscall_64_after_call */
        jmp     *%r12

.Ldo_syscall_64_after_call:
        /* switch to entry stack */
        movq    CPU_ENTRY_AREA_tss + TSS_sp0 + CPU_ENTRY_AREA, %rsp
        subq    $SIZEOF_PTREGS, %rsp

        /* save return value */
        movq    %rax, RAX(%rsp)

        /* switch to user page table */
        RESTORE_CR3 save_reg=%r14

.Ldo_syscall_64_return:
        POP_EXTRA_REGS
        POP_C_REGS

        /* restore user %rsp */
        movq    RSP_SCRATCH, %rsp

        swapgs
        sysretq
END(do_syscall_64)

.popsection

.section .entry.text, "ax"

/*
 * Interrupt entry/exit.
 *
 * Entry runs with interrupts off.
 */

/* 0(%rsp): ~(interrupt number) */
.macro interrupt func
        /* must have entered from user mode */
        testb   $3, CS-ORIG_RAX(%rsp)
        1: jz      1b

        swapgs

        ALLOC_PT_GPREGS_ON_STACK
        SAVE_C_REGS
        SAVE_EXTRA_REGS

        /* save pointer to struct pt_regs */
        movq    %rsp, %rdi

        SAVE_AND_SWITCH_TO_KERNEL_CR3 scratch_reg=%rax save_reg=%r14

        movq    PER_CPU_VAR(cpu_tss + TSS_sp1), %rsp

        /* save RIP-relative to retint_user in %r12 */
        leaq    retint_user(%rip), %r12

        RELOCATE_TO_KERNEL_RIP scratch_reg=%rax

        call    \func

        /* relocate to ret_user (RIP-relative) */
        jmp     *%r12
.endm

/*
 * APIC interrupts.
 */
.macro apicinterrupt num sym do_sym
ENTRY(\sym)
        pushq   $~(\num)
        interrupt \do_sym
END(\sym)
.endm

apicinterrupt LOCAL_TIMER_VECTOR                apic_timer_interrupt            smp_apic_timer_interrupt

apicinterrupt ERROR_APIC_VECTOR                 error_interrupt                 smp_error_interrupt
apicinterrupt SPURIOUS_APIC_VECTOR              spurious_interrupt              smp_spurious_interrupt

/*
 * Exception entry points.
 */

.macro idtentry sym do_sym has_error_code:req
ENTRY(\sym)
        .if \has_error_code == 0
        pushq   $-1                             /* ORIG_RAX */
        .endif

        ALLOC_PT_GPREGS_ON_STACK

        /* don't touch any registers other than %rsp before this point */
        call     error_entry
        /*
         * On exit:
         * %ebx=0: need swapgs on exit, ebx=1: don't need it
         * %rdi: pointer to struct pt_regs
         * %r12: %rip for error_exit
         * %r14: user %cr3 (if coming from user)
         */

        /* relocate to identity mapping (no-op if already in kernel) */
        RELOCATE_TO_KERNEL_RIP scratch_reg=%rax

        .if \has_error_code
        movq    ORIG_RAX(%rdi), %rsi            /* get error code */
        .else
        xorl    %esi, %esi                      /* no error code */
        .endif

        call    \do_sym

        /* relocate to error_exit (RIP-relative) */
        jmp     *%r12
END(\sym)
.endm

idtentry divide_error                   do_divide_error                 has_error_code=0
idtentry overflow                       do_overflow                     has_error_code=0
idtentry bounds                         do_bounds                       has_error_code=0
idtentry invalid_op                     do_invalid_op                   has_error_code=0
idtentry device_not_available           do_device_not_available         has_error_code=0
idtentry double_fault                   do_double_fault                 has_error_code=1
idtentry coprocessor_segment_overrun    do_coprocessor_segment_overrun  has_error_code=0
idtentry invalid_TSS                    do_invalid_TSS                  has_error_code=1
idtentry segment_not_present            do_segment_not_present          has_error_code=1
idtentry spurious_interrupt_bug         do_spurious_interrupt_bug       has_error_code=0
idtentry coprocessor_error              do_coprocessor_error            has_error_code=0
idtentry alignment_check                do_alignment_check              has_error_code=1
idtentry simd_coprocessor_error         do_simd_coprocessor_error       has_error_code=0

/* no nmi, debug  */
idtentry int3                           do_int3                         has_error_code=0
idtentry stack_segment                  do_stack_segment                has_error_code=1

idtentry general_protection             do_general_protection           has_error_code=1
idtentry page_fault                     do_page_fault                   has_error_code=1

/*
 * Save all registers in pt_regs, and switch gs if needed.
 * Return: EBX=0: came from user mode; EBX=1: otherwise
 */
ENTRY(error_entry)
        cld
        SAVE_C_REGS 8
        SAVE_EXTRA_REGS 8

        /* save pt_regs in %rdi */
        leaq    8(%rsp), %rdi
        /* save RIP-relative to error_exit in %r12 */
        leaq    error_exit(%rip), %r12

        xorl    %ebx, %ebx
        testb   $3, CS+8(%rsp)
        jz      .Lerror_kernelspace

        /* entered from user mode */
        swapgs
        SAVE_AND_SWITCH_TO_KERNEL_CR3 scratch_reg=%rax save_reg=%r14

        /* switch from entry stack to kernel stack; also transfer return address */
        popq    %rax
        movq    PER_CPU_VAR(cpu_tss + TSS_sp1), %rsp
        pushq   %rax
        ret

.Lerror_kernelspace:
        incl    %ebx

        /*
         * Be paranoid: we shouldn't have exceptions or interrupts in kernel,
         * so just get a sane environment for printing out panic messages.
         */
        SAVE_AND_SWITCH_TO_KERNEL_CR3 scratch_reg=%rax save_reg=%r14
        /* NB: what about %gs? */
        ret
END(error_entry)

/*
 * On entry:
 * %ebx is a "return to kernel mode" flag:
 *   1: already in kernel mode, don't need SWAPGS
 *   0: user gsbase is loaded, we need SWAPGS and standard preparation for return to usermode
 * If coming from user:
 * %rip is already offseted
 * %r14 holds user %cr3
 */
ENTRY(error_exit)
        testl   %ebx, %ebx
        jnz     retint_kernel

retint_user:
        /* switch from kernel stack to entry stack (must occur before %cr3 switch) */
        movq    PER_CPU_VAR(cpu_tss + TSS_sp0), %rsp
        subq    $SIZEOF_PTREGS, %rsp

        /* switch to user %cr3 (must occur after relocation) */
        RESTORE_CR3 save_reg=%r14
        swapgs

retint_kernel:
        POP_EXTRA_REGS
        POP_C_REGS
        addq    $8, %rsp        /* skip regs->orig_ax */
        iretq
END(error_exit)

/* ignore 32-bit syscalls */
ENTRY(do_syscall_32)
        mov     $-ENOSYS, %eax
        sysret
END(do_syscall_32)

/*
 * %rdi: pointer to struct pt_regs
 * %rsi: new %cr3
 */
ENTRY(return_to_usermode)
        /* Save user %cr3 in %r14 for retint_user.  */
        movq    %rsi, %r14

        /* Copy struct pt_regs to entry stack.
         *   memcpy(tss.sp0 - sizeof(struct pt_regs), regs, sizeof(struct pt_regs))
         * %rdi: entry stack address
         * %rsi: given struct pt_regs
         * %rdx: sizeof(struct pt_regs)
         */
        movq    $SIZEOF_PTREGS, %rdx
        movq    %rdi, %rsi
        movq    PER_CPU_VAR(cpu_tss + TSS_sp0), %rdi
        subq    $SIZEOF_PTREGS, %rdi
        call    memcpy

        /*
         * Jump to offseted retint_user.
         *
         * As __entry_text_start is mapped to:
         *   CPU_ENTRY_AREA_END - (__entry_text_end - __entry_text_start)
         * the %rip offset is:
         *   CPU_ENTRY_AREA_END - __entry_text_end
         */
        movabsq $CPU_ENTRY_AREA_END, %rax
        subq    $__entry_text_end, %rax
        addq    $retint_user, %rax
        jmp     *%rax
END(return_to_usermode)
