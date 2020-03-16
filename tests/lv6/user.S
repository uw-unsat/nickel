#include <io/linkage.h>

GLOBAL(user_start)
        mov     $0, %rax
        vmcall
        mov     $481, %rdi
        mov     $0, %rax
        syscall
        mov     $1, %rax
        vmcall
        mov     $451, %rdi
        mov     $1, %rax
        syscall
        1: jmp 1b
GLOBAL(user_end)
