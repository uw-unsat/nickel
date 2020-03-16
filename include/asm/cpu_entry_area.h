#pragma once

#include <asm/setup.h>
#include <asm/desc.h>
#include <asm/processor.h>

#define CPU_ENTRY_AREA_IDT      CPU_ENTRY_AREA_START
#define CPU_ENTRY_AREA_PER_CPU  (CPU_ENTRY_AREA_IDT + PAGE_SIZE)
#define CPU_ENTRY_AREA_TEXT     (CPU_ENTRY_AREA_END - (__entry_text_end - __entry_text_start))

struct entry_stack {
        uint64_t stack[64];
} __aligned(PAGE_SIZE);

struct tss_page {
        struct tss tss;
} __aligned(PAGE_SIZE);

/*
 * cpu_entry_area is a percpu region that contains things needed by the CPU
 * and early entry/exit code.  Real types aren't used for all fields here
 * to avoid circular header dependencies.
 *
 * Every field is a virtual alias of some other allocated backing store.
 * There is no direct allocation of a struct cpu_entry_area.
 */
struct cpu_entry_area {
        uint8_t gdt[PAGE_SIZE];

        /*
         * The GDT is just below entry_stack and thus serves as
         * a read-only guard page.
         */
        struct entry_stack entry_stack;

        struct tss_page tss;

        uint8_t entry_trampoline[PAGE_SIZE];

        /* exception stacks used for IST entries */
        uint8_t exception_stacks[NR_EXCEPTION_STACKS][EXCEPTION_STACK_SIZE];
};

struct cpu_entry_area *get_cpu_entry_area(int cpu);
void cea_set_pte(void *cea_vaddr, phys_addr_t pa, pteval_t prot);
void cea_map_pages(void *cea_vaddr, phys_addr_t pa, size_t pages, pteval_t prot);

static inline uintptr_t cpu_entry_area_text_address(const void *va)
{
        return (uintptr_t)va + (CPU_ENTRY_AREA_TEXT - (uintptr_t)__entry_text_start);
}
