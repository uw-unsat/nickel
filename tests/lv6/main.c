#include <asm/init.h>
#include <asm/processor.h>
#include <asm/segment.h>
#include <asm/setup.h>
#include <asm/traps.h>
#include <io/mmu.h>
#include <sys/string.h>

/* user page table */
static pteval_t upml4[512] __aligned(PAGE_SIZE);
static pteval_t pdpt[512] __aligned(PAGE_SIZE);
static pteval_t pd[512] __aligned(PAGE_SIZE);
static pteval_t pt[512] __aligned(PAGE_SIZE);
/* user data */
static char user_data[PAGE_SIZE] __aligned(PAGE_SIZE);
/* kernel page table */
extern pteval_t kpml4[];
/* user code (defined in user.S) */
extern char user_start[], user_end[];

static noreturn void user_init(void)
{
        struct pt_regs regs = {
                /* user segments */
                .cs     = USER_CS,
                .ss     = USER_DS,
                /* assume user code starts at virtual address 4M */
                .rip    = SZ_4M,
                .rflags = X86_RFLAGS_IF,
        };
        size_t cea_index = pml4_index(CPU_ENTRY_AREA_START);

        /* map cpu entry area */
        upml4[cea_index] = kpml4[cea_index];

        /* map virtual address 4M in user page table */
        upml4[0] = __pa(pdpt) | PTE_PRESENT | PTE_RW | PTE_USER;
        pdpt[0] = __pa(pd) | PTE_PRESENT | PTE_RW | PTE_USER;
        pd[2] = __pa(pt) | PTE_PRESENT | PTE_RW | PTE_USER;
        pt[0] = __pa(user_data) | PTE_PRESENT | PTE_RW | PTE_USER;

        /* load user code */
        memcpy(user_data, user_start, user_end - user_start);

        /* start user space with given register valeus & user page table */
        return_to_usermode(&regs, __pa(upml4));
}

noreturn void main(void)
{
        uart8250_init();
        vgacon_init();

        cpu_init();
        tsc_init();

        pr_info("booting...\n");

        trap_init();
        syscall_init();

        user_init();
};
