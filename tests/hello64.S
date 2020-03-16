#include <asm/msr-index.h>
#include <asm/processor-flags.h>
#include <asm/segment.h>
#include <sys/multiboot.h>
#include <io/linkage.h>
#include <io/sizes.h>
#include <io/mmu.h>

#define MULTIBOOT_HEADER_FLAGS  (MULTIBOOT_PAGE_ALIGN | MULTIBOOT_AOUT_KLUDGE)

        .code32
ENTRY(_start)
        jmp     start_multiboot

        .balign 4
header:
        .long   MULTIBOOT_HEADER_MAGIC
        .long   MULTIBOOT_HEADER_FLAGS
        .long   - (MULTIBOOT_HEADER_MAGIC + MULTIBOOT_HEADER_FLAGS)
        .long   header
        .long   _start
        .long   _end
        .long   _end
        .long   _start

start_multiboot:
        /* CR4: enable PAE, PSE */
        movl    %cr4, %eax
        orl     $(X86_CR4_PAE|X86_CR4_PSE), %eax
        movl    %eax, %cr4

        /* CR3: load boot page table */
        movl    $pml4, %eax
        movl    %eax, %cr3

        lgdt    gdt

        /* MSR EFER: enable LME */
        movl    $MSR_EFER, %ecx
        rdmsr
        orl     $EFER_LME, %eax
        wrmsr

        /* CR0: enable PG, WP, NE */
        movl    %cr0, %eax
        orl     $(X86_CR0_PG|X86_CR0_WP|X86_CR0_NE), %eax
        movl    %eax, %cr0

        movl    $BOOT_DS, %eax
        movw    %ax, %ss
        movw    %ax, %ds
        movw    %ax, %es

        /* enter 64-bit mode */
        ljmp    $BOOT_CS, $start_64

        .code64
start_64:
        cld
        lea     msg(%rip), %rsi
        mov     $(msg_end - msg), %rcx
        mov     $0xe9, %dx
        rep outsb

        mov     $0, %ax
        mov     $0x501, %dx
        outb    %al, %dx
        1:
        hlt
        jmp     1b

msg:
        .ascii  "Hello from long mode!\n"
msg_end:

/* boot GDT */
        .balign 8
gdt:
        .word   gdt_end - gdt - 1
        .long   gdt
        .word   0
        .quad   0
        .quad   0x00af9a000000ffff      /* BOOT_CS */
        .quad   0x00cf92000000ffff      /* BOOT_DS */
        .quad   0x0080890000000000      /* TS descriptor */
        .quad   0x0000000000000000      /* TS continued */
gdt_end:

/* boot page table */
        .balign SZ_4K
pml4:
        .quad   pml3 + PTE_PRESENT + PTE_RW
        .rept   512 - 1
        .quad   0
        .endr

pml3:
        index = 0
        .rept   4
        .quad   pml2 + (index * SZ_4K) + PTE_PRESENT + PTE_RW
        index = index + 1
        .endr
        .rept   512 - 4
        .quad   0
        .endr

pml2:
        index = 0
        .rept   512 * 4
        .quad   (index * SZ_2M) + PTE_PRESENT + PTE_RW + PTE_PSE
        index = index + 1
        .endr

end_:
