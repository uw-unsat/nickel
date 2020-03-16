#include <asm/setup.h>
#include <io/mmu.h>
#include <sys/errno.h>
#include <sys/string.h>
#include "param.h"
#include "proc.h"
#include "vm.h"

#define PTE_DEFAULT_UMASK       (PTE_PRESENT | PTE_USER | PTE_RW)

static uint64_t pml4[512] __aligned(SZ_4K);
static uint64_t pdpt[512] __aligned(SZ_4K);
static uint64_t proc_pd[NR_PROCS][512] __aligned(SZ_4K);

static struct page pages[NR_PAGES];
static uint8_t page_data[NR_PAGES][SZ_2M] __aligned(SZ_2M);

void vm_init(void)
{
        extern pteval_t kpml4[];
        size_t cea_index = pml4_index(CPU_ENTRY_AREA_START);

        pml4[0] = __pa(pdpt) | PTE_DEFAULT_UMASK;
        pml4[cea_index] = kpml4[cea_index];
}

noreturn void vm_switch(uint64_t pid)
{
        current_pid = pid;
        pdpt[0] = __pa(proc_pd[pid]) | PTE_DEFAULT_UMASK;
        return_to_usermode(&get_proc(pid)->cpu, __pa(pml4));
}

static long __vm_alloc(uint64_t pid, size_t slot, uint64_t pageid)
{
        struct proc *proc = get_proc(pid);
        uint64_t *pd = proc_pd[pid];
        phys_addr_t paddr;

        if (!proc->nr_free_pages)
                return -ENOMEM;
        if (slot >= 512)
                return -EINVAL;
        if (pd[slot])
                return -EACCES;
        if (pageid >= NR_PAGES)
                return -EINVAL;
        if (pages[pageid].owner)
                return -EINVAL;

        --proc->nr_free_pages;

        paddr = __pa(page_data) + pageid * SZ_2M;
        pd[slot] = paddr | PTE_PSE | PTE_DEFAULT_UMASK;
        return 0;
}

long vm_alloc(uint64_t pid, size_t slot)
{
        static size_t counter;
        size_t pageid = counter;
        long r;

        r = __vm_alloc(pid, slot, pageid);
        if (r < 0)
                return r;
        ++counter;
        return pageid;
}

void *vm_get_data(uint64_t pageid)
{
        return page_data[pageid];
}
