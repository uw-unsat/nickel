#include <io/linkage.h>
#include <io/sizes.h>

ENTRY(_start)
        leaq    stack_top(%rip), %rsp
        movq    $0, %rbp
        call    translate_test_enclave
END(_start)

.section .bss
.balign SZ_4K
        .space  SZ_4K
stack_top:
