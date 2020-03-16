#include <io/linkage.h>
#include <mcertikos/memlayout.h>

ENTRY(_start)
        movq    $0, %rbp
        movq    $USER_STACK_TOP, %rsp
        call    main
1:
        call    yield
        jmp     1b
ENDPROC(_start)
