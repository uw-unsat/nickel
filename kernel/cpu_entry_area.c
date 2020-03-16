#include <asm/cpu_entry_area.h>

extern pteval_t kpml4[];

struct cpu_entry_area *get_cpu_entry_area(int cpu)
{
        uintptr_t va = CPU_ENTRY_AREA_PER_CPU + cpu * sizeof(struct cpu_entry_area);

        BUILD_BUG_ON(sizeof(struct cpu_entry_area) % PAGE_SIZE != 0);

        return (struct cpu_entry_area *)va;
}

void cea_set_pte(void *cea_vaddr, phys_addr_t pa, pteval_t prot)
{
        uintptr_t va = (uintptr_t)cea_vaddr;
        pteval_t *entries, entry;

        BUG_ON(va < CPU_ENTRY_AREA_START);
        BUG_ON(va >= CPU_ENTRY_AREA_END);
        BUG_ON(va % PAGE_SIZE);
        BUG_ON(pa % PAGE_SIZE);

        entries = kpml4;
        entry = entries[pml4_index(va)];
        BUG_ON(!(entry & PTE_PRESENT));

        entries = __va(entry & PTE_PFN_MASK);
        entry = entries[pdpt_index(va)];
        BUG_ON(!(entry & PTE_PRESENT));

        entries = __va(entry & PTE_PFN_MASK);
        entry = entries[pd_index(va)];
        BUG_ON(!(entry & PTE_PRESENT));

        entries = __va(entry & PTE_PFN_MASK);
        BUG_ON(entries[pt_index(va)]);
        entries[pt_index(va)] = pa | prot;
}

void cea_map_pages(void *cea_vaddr, phys_addr_t pa, size_t pages, pteval_t prot)
{
        for ( ; pages; pages--, cea_vaddr += PAGE_SIZE, pa += PAGE_SIZE)
                cea_set_pte(cea_vaddr, pa, prot);
}
