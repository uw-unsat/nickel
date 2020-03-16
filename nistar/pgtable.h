#pragma once

#include "mm.h"

DEFINE_SAFE_TYPE(pte, uint64_t);

struct pgtable {
        pte_t ptes[PGTABLE_NR_PTES];
} __aligned(SZ_4K);

bool pte_permitted(pteval_t pteval, bool super);
int pgtable_link(struct pgtable *pgtable, size_t slot, page_id_t blkid, pteval_t perm);
int pgtable_ksymlink_link(struct pgtable *pgtable, size_t slot, ksymlink_t blkid, pteval_t perm);
