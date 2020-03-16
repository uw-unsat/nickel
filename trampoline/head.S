#include <asm/processor-flags.h>
#include <asm/segment.h>
#include <asm/setup.h>
#include <io/linkage.h>

#define TRAMPOLINE_SEG          0

        .text
        .code16
ENTRY(_start)
        cli
        wbinvd
        /* normalize the address */
        ljmp    $TRAMPOLINE_SEG, $1f

1:
        mov     %cs, %ax
        mov     %ax, %ds
        mov     %ax, %es
        mov     %ax, %ss

        lgdt    gdt

        movl    %cr0, %eax
        orl     $X86_CR0_PE, %eax
        movl    %eax, %cr0

        mov     $BOOT_DS, %ax
        mov     %ax, %ds
        mov     %ax, %es
        mov     %ax, %ss
        mov     %ax, %fs
        mov     %ax, %gs

        ljmp    $BOOT_CS, $2f

        .code32
2:
        /* no multiboot */
        xorl    %eax, %eax
        xorl    %ebx, %ebx
        jmp     end


        .balign 8
gdt:
        .word   gdt_end - gdt - 1
        .long   gdt
        .word   0
        .quad   0
        .quad   0x00cf9a000000ffff      /* 32-bit CS */
        .quad   0x00cf92000000ffff      /* 32-bit DS */
gdt_end:

end:
        .byte   0xe9
        .long   end - _end              /* filled in by vmm/kernel */
_end:
