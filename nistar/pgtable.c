#include <sys/errno.h>
#include "block.h"
#include "pgtable.h"

bool pte_permitted(pteval_t pteval, bool super)
{
        pteval_t must = PTE_PRESENT | PTE_USER | (super ? PTE_PSE : 0);
        pteval_t may = must | PTE_RW | PTE_PWT | PTE_PCD | PTE_NX | PTE_BIT_SOFTW1 | PTE_BIT_SOFTW2 | PTE_BIT_SOFTW3;

        if ((pteval & must) != must)
                return false;
        if (pteval & ~may)
                return false;
        return true;
}

int pgtable_link(struct pgtable *pgtable, size_t slot, page_id_t blkid, pteval_t perm)
{
        /* assume 2MB pages */
        BUG_ON(!page_is_type(blkid, PAGE_TYPE_BLOCK));

        if (!(slot < PGTABLE_NR_PTES))
                return -EINVAL;

        /* page permission checking */
        if (!pte_permitted(perm, true))
                return -EINVAL;

        /* must be an empty slot */
        /* if (pte_val(pgtable->ptes[slot])) */
        /*         return -EINVAL; */

        pgtable->ptes[slot] = __pte((block_to_pfn(blkid) << PTE_PFN_SHIFT) | perm);
        return 0;
}

int pgtable_ksymlink_link(struct pgtable *pgtable, size_t slot, ksymlink_t blkid, pteval_t perm)
{
        BUG_ON(!ksymlink_is_type(blkid, PAGE_TYPE_BLOCK));

        /* validate symlink */
        if (!ksymlink_is_type(blkid, PAGE_TYPE_BLOCK))
                return -EINVAL;

        return pgtable_link(pgtable, slot, blkid.page.id, perm);
}
