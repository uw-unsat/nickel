#include <asm/setup.h>

OUTPUT_ARCH(i386:x86-64)
ENTRY(_start)

SECTIONS
{
        . = TRAMPOLINE_START;
        .text : {
                *(.text .text.*)
        }
        .rodata : {
                *(.rodata .rodata.*)
        }
        .data : {
                *(.data .data.*)
        }
        .bss : {
                *(.bss .bss.*)
        }
}
