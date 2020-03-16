#include <nistar/memlayout.h>
#include <nistar/env.h>
#include <nistar/ulib.h>
#include <io/mmu.h>
#include <io/sizes.h>
#include <stdint.h>

static uintptr_t __cur_brk = BRK_START;
static size_t pmd_watermark = 0;

#define ADDR(p) ((BRK_START) + (SZ_2M * (p)))

uintptr_t hs_brk(uintptr_t newbrk)
{
        long r;

        if (newbrk == 0)
                return __cur_brk;

        ASSERT_MSG(newbrk >= ADDR(0), "__brk invalid argument");

        static usymlink_t brk_pmd = USYMLINK_INVALID;
        if (!usymlink_is_valid(brk_pmd)) {
                ASSERT_MSG(page_walk(__cur_brk, &brk_pmd) == 0, "brk");
        }

        if (newbrk > __cur_brk) {
                while (ADDR(pmd_watermark) <= newbrk) {
                        /* new block to allocate */
                        usymlink_t blk;
                        struct label secrecy, integrity;
                        self_get_label(&secrecy, &integrity, NULL);
                        r = alloc_block(&blk, self_get_internal_container(), &secrecy, &integrity, "heap");
                        ASSERT_MSG(r == 0, "alloc_block");
                        if (directory_link_block(brk_pmd, pmd_watermark++, blk, PTE_PRESENT | PTE_RW | PTE_USER | PTE_PSE)) {
                                ASSERT_MSG(false, "Could not allocate block for brk");
                                return -1;
                        }
                }

        }

        __cur_brk = newbrk;

        return __cur_brk;
}

