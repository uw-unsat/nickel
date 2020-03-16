#pragma once

#include <sys/types.h>

#define E820_MAX_ENTRIES        128

#ifndef __ASSEMBLER__

/*
 * These are the E820 types known to the kernel:
 */
enum e820_type {
        E820_TYPE_RAM           = 1,
        E820_TYPE_RESERVED      = 2,
        E820_TYPE_ACPI          = 3,
        E820_TYPE_NVS           = 4,
        E820_TYPE_UNUSABLE      = 5,
        E820_TYPE_PMEM          = 7,
};

/*
 * A single E820 map entry, describing a memory range of [addr...addr+size-1],
 * of 'type' memory type:
 */
struct e820_entry {
        uint64_t                addr;
        uint64_t                size;
        uint32_t                type;
} __packed;


struct e820_table {
        uint32_t nr_entries;
        struct e820_entry entries[E820_MAX_ENTRIES];
};

extern struct e820_table e820_table;

extern bool e820_mapped_all(uint64_t start, uint64_t end, enum e820_type type);

extern void e820_range_add(uint64_t start, uint64_t size, enum e820_type type);
extern uint64_t e820_range_update(uint64_t start, uint64_t size, enum e820_type old_type, enum e820_type new_type);

extern void e820_print_table(char *who);
extern void e820_update_table(void);
extern void e820_update_table_print(void);
extern unsigned long e820_end_of_ram_pfn(void);

struct multiboot_mmap_entry;

void e820_range_add_multiboot(struct multiboot_mmap_entry *e, size_t len);

#endif  /* !__ASSEMBLER__ */
