#include <nistar/memlayout.h>
#include <io/linkage.h>
#include <io/sizes.h>
#include "asm-offsets.h"

ENTRY(__nistar_syscall)
        movq %rdi, %rax
        movq %rsi, %rdi
        movq %rdx, %rsi
        movq %rcx, %rdx
        movq %r8, %r10
        movq %r9, %r8
        movq 8(%rsp), %r9
        syscall
        ret
ENDPROC(__nistar_syscall)

ENTRY(__sys_gate_call)
        movq %rcx, %r10
        movq $SYS_gate_enter, %rax
        syscall
        ret
ENDPROC(__sys_gate_call)

ENTRY(__nistar_sys_gate_call_ret)
        /* move caller gate argument (%rdx)
           as return value */
        movq %rdx, %rax
        ret
ENDPROC(__nistar_sys_gate_call_ret)

ENTRY(__sys_gate_enter)
        movq $SYS_gate_enter, %rax
        movq %rcx, %r10
        movq %r9, %rsp
        syscall

        /* TODO: return, the stack has already been changed.
           if the syscall fails, need to restore the old stack so we can
           return..  */
        ud2
        1:
        jmp 1b

        ret
ENDPROC(__sys_gate_enter)

ENTRY(_gate_entry)
        mov %rdi, %rax
        mov %rsi, %rdi
        mov %rdx, %rsi
        mov %rcx, %rdx
        call *%rax;
        movq $SYS_gate_enter, %rdi
        /* return gate is on the stack at gate entry */
        movq 8(%rsp), %rsi
        movq 16(%rsp), %rdx
        movq 24(%rsp), %rcx
        movq 32(%rsp), %r8
        /* return value from gate call function as gate arg */
        movq %rax, %r9
        jmp __nistar_syscall

        ud2
        1:
        jmp 1b
ENDPROC(_gate_entry)

/* Gate entry point that sets the TLS contents
   and calls a callback function.

   %rsi : the base of a 2M region to copy to the TLS
   %rdi : callback fn pointer
   %rdx : sp
 */
ENTRY(_gate_entry_with_tls)
        movq %rsi, %rsp
        addq $256, %rsp // temporary stack space for memcpy
        pushq %rdx
        pushq %rdi

        // Copy %rsi to TLS
        movq $(USER_TLS_END - SZ_2M), %rdi
        movq $SZ_2M, %rdx
        callq memcpy

        // callback fn and stack
        popq %rax
        popq %rsp

        // pop arguments from the stack
        popq %rdi
        popq %rsi
        popq %rdx
        popq %rcx
        popq %r8
        popq %r9

        jmp *%rax

        ud2
        1:
        jmp 1b
ENDPROC(_gate_entry_with_tls)

ENTRY(_gate_fork_entry)
        movq %rsi, %rsp
        addq $256, %rsp // temporary stack space for memcpy
        pushq %rdx

        // Copy %rsi to TLS
        movq $(USER_TLS_END - SZ_2M), %rdi
        movq $SZ_2M, %rdx
        callq memcpy

        popq %rsp

        // restore callee saved registers from the stack
        movq (%rsp), %rbp
        movq 8(%rsp), %rbx
        movq 16(%rsp), %r12
        movq 24(%rsp), %r13
        movq 24(%rsp), %r14
        movq 32(%rsp), %r15

        // Anything that has to be reset in the AS?

        movq $0, %rax
        leave
        ret

        ud2
        1:
        jmp 1b
ENDPROC(_gate_fork_entry)
