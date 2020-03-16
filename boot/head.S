#include <asm/msr-index.h>
#include <asm/processor-flags.h>
#include <asm/segment.h>
#include <asm/setup.h>
#include <asm/threads.h>
#include <io/linkage.h>
#include <io/sizes.h>
#include <sys/multiboot.h>

#define MULTIBOOT_HEADER_FLAGS  (MULTIBOOT_PAGE_ALIGN | MULTIBOOT_MEMORY_INFO | MULTIBOOT_AOUT_KLUDGE)

        .section .head.text
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
        .long   _edata
        .long   _end
        .long   _start

/*
 * eax: magic value
 * ebx: physical address of the multiboot structure
 */
start_multiboot:
        /* save multiboot pointer */
        movl    %eax, %edi
        movl    %ebx, %esi

        /* CR4: enable PAE, PSE */
        movl    %cr4, %eax
        orl     $(X86_CR4_PAE|X86_CR4_PSE), %eax
        movl    %eax, %cr4

        /* CR3: load boot page table */
        movl    $kpml4, %eax
        movl    %eax, %cr3

        lgdt    gdt

        /* MSR EFER: enable LME, NX */
        movl    $MSR_EFER, %ecx
        rdmsr
        orl     $(EFER_LME|EFER_NX), %eax
        wrmsr

        /* no need to load TSS */

        /* CR0: enable PG, WP, NE */
        movl    %cr0, %eax
        orl     $(X86_CR0_PG|X86_CR0_WP|X86_CR0_NE), %eax
        movl    %eax, %cr0

        movl    $BOOT_DS, %eax
        movw    %ax, %ss
        movw    %ax, %ds
        movw    %ax, %es
        xorl    %eax, %eax
        movw    %ax, %fs
        movw    %ax, %gs

        /* enter 64-bit mode */
        ljmp    $BOOT_CS, $start_64

        .code64
start_64:
        /* set up %gs */
        movl    $MSR_GS_BASE, %ecx
        movl    initial_gs(%rip), %eax
        movl    initial_gs+4(%rip), %edx
        wrmsr

        /* set stack */
        movq    initial_stack(%rip), %rsp
        movq    $0x0, %rbp
        call    main
        call    die
        1:
        jmp     1b

/* boot GDT */
        .balign 8
gdt:
        .word   gdt_end - gdt - 1
        .long   gdt
        .word   0
        .quad   0
        .quad   0x00af9a000000ffff      /* BOOT_CS */
        .quad   0x00cf92000000ffff      /* BOOT_DS */
gdt_end:

/* boot page table */

        .balign SZ_4K
GLOBAL(kpml4)
        .quad   kpdpt + PTE_PRESENT + PTE_RW
        .rept   512 - 2
        .quad   0
        .endr
        /* cpu_entry_area mapping */
        .quad   entry_pdpt + PTE_PRESENT + PTE_RW

kpdpt:
        index = 0
        .rept   4
        .quad   kpd + (index * SZ_4K) + PTE_PRESENT + PTE_RW
        index = index + 1
        .endr
        .rept   512 - 4
        .quad   0
        .endr

kpd:
        index = 0
        .rept   512 * 4
        .quad   (index * SZ_2M) + PTE_PRESENT + PTE_RW + PTE_PSE
        index = index + 1
        .endr

entry_pdpt:
        .quad   entry_pd + PTE_PRESENT + PTE_RW
        .rept   512 - 1
        .quad   0
        .endr

entry_pd:
        .quad   entry_pt + PTE_PRESENT + PTE_RW
        .rept   512 - 1
        .quad   0
        .endr

entry_pt:
        .space  SZ_4K
