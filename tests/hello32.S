#include <sys/multiboot.h>

#define MULTIBOOT_HEADER_FLAGS  MULTIBOOT_PAGE_ALIGN

        .balign 4
        .long   MULTIBOOT_HEADER_MAGIC
        .long   MULTIBOOT_HEADER_FLAGS
        .long   - (MULTIBOOT_HEADER_MAGIC + MULTIBOOT_HEADER_FLAGS)

        .global _start
        .code32
_start:
        cld
        lea     msg, %esi
        mov     $(msg_end - msg), %ecx
        mov     $0xe9, %dx
        rep outsb

        mov     $0, %ax
        mov     $0x501, %dx
        outb    %al, %dx
        1:
        hlt
        jmp     1b

msg:
        .ascii  "Hello from protected mode!\n"
msg_end:
