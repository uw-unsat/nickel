#pragma once

#include <asm/e820.h>
#include <io/sizes.h>

#define VMM_START               0x10000000
#define KERNEL_START            0x00100000
#define TRAMPOLINE_START        0x00008000
#define FIRMWARE_START          0x00001000

/*
 * This applies to every address shared by user and kernel,
 * such as GDT, IDT, TSS, and entry code.
 */
#define CPU_ENTRY_AREA_START    UINT64_C(0xffffff8000000000)
#define CPU_ENTRY_AREA_END      (CPU_ENTRY_AREA_START + SZ_2M)

#define NR_syscalls             128
#define NR_hypercalls           128

#define CMDLINE_SIZE            1024
#define E820_MAX_ENTRIES_GUEST  128

#ifndef __ASSEMBLER__

struct guest_params {
        uint8_t magic[8];
        uint64_t kernel_start;
        uint64_t kernel_end;
        uint64_t initrd_start;
        uint64_t initrd_end;
        uint8_t cmdline[CMDLINE_SIZE];
        uint32_t e820_entries;
        struct e820_entry e820_table[E820_MAX_ENTRIES_GUEST];
} __packed;

extern struct guest_params guest_params;

#endif  /* !__ASSEMBLER__ */
