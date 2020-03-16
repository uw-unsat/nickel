#include <io/linkage.h>

        .section .rodata

GLOBAL(_binary_trampoline_start)
        .incbin "trampoline.bin"
GLOBAL(_binary_trampoline_end)
