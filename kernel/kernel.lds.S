#include <sys/vmlinux.lds.h>

OUTPUT_ARCH(i386:x86-64)
ENTRY(_start)

SECTIONS
{
        . = KERNEL_START;
        .text : {
                HEAD_TEXT
                TEXT_TEXT
                ENTRY_TEXT
                ENTRY_TRAMPOLINE
        }
        .rodata : {
                *(.rodata .rodata.*)
        }
        .data : {
                DATA_DATA
                _edata = .;
        }
        . = ALIGN(PAGE_SIZE);
        .percpu : {
                __per_cpu_start = .;
                *(.percpu .percpu.*)
                . = ALIGN(PAGE_SIZE);
                __per_cpu_end = .;
        }
        . += (NR_CPUS - 1) * (__per_cpu_end - __per_cpu_start);
        .bss : {
                *(.bss .bss.*)
        }
        . = ALIGN(PAGE_SIZE);
        _end = .;
}
