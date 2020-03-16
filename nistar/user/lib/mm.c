#include <errno.h>
#include <nistar/memlayout.h>
#include <nistar/env.h>
#include <nistar/ulib.h>
#include <io/sizes.h>
#include <sys/types.h>

long alloc_internal_block(usymlink_t *sym)
{
        long r;
        // TODO: labels
        struct label secrecy, integrity, ownership;
        self_get_label(&secrecy, &integrity, &ownership);
        if ((r = alloc_block(sym, self_get_internal_container(), &secrecy, &integrity, "internal")) < 0)
                return r;
        ASSERT_MSG(r == 0, "alloc_block");
        return r;
}

long page_walk(uintptr_t va, usymlink_t *pmd)
{
        long r;
        size_t pudslot;
        usymlink_t upud;
        // TODO: what should the labels be?
        // Inherit from the thread?
        // Inherit from the parent container / directory
        struct label secrecy, integrity, ownership;
        self_get_label(&secrecy, &integrity, &ownership);

        ASSERT_MSG(pml4_index(va) == 0, "page_walk: va to large");
        pudslot = pud_index(va);

        upud = self_get_pud();

        r = directory_get_slot(upud, pudslot, pmd);
        if (r != 0) {
                r = alloc_directory_pmd(pmd, self_get_internal_container(), &secrecy, &integrity, NULL);
                ASSERT_MSG (r == 0, "alloc_directory_pmd");
                if (r) return r;
                r = directory_link_pmd(upud, pudslot, *pmd);
                ASSERT_MSG (r == 0, "directory_link_pmd");
                if (r) return r;
        }
        return 0;
}

long map_pages(uintptr_t va, size_t n, pteval_t perm)
{
        usymlink_t upmd, ublk;
        size_t i;
        long r;

        ASSERT_MSG(va % SZ_2M == 0, "va must be block-aligned");
        for (i = 0; i < n; i += SZ_2M, va += SZ_2M) {
                r = page_walk(va, &upmd);
                ASSERT_MSG(r == 0, "page_walk");
                if (r) return r;
                r = alloc_internal_block(&ublk);
                ASSERT_MSG(r == 0, "alloc_internal_block");
                if (r) return r;
                r = directory_link_block(upmd, pmd_index(va), ublk, perm);
                if (r == -EEXIST)
                    return r;
                ASSERT_MSG(r == 0, "sys_directory_link_block");
                if (r) return r;
        }
        return 0;
}

long unmap_pages(uintptr_t va, size_t len)
{
        long r;
        usymlink_t pmd, block;
        size_t n, startidx = pmd_index(va);
        size_t nr_pages = roundup(len, SZ_2M) / SZ_2M;
        ASSERT_MSG(startidx + nr_pages < DIRECTORY_NR_ENTRIES, "unmap pages: range too large");
        r = page_walk(va, &pmd);
        ASSERT_MSG(r == 0, "page_walk");
        for (n = startidx; n < startidx + nr_pages; n++) {
                r = directory_get_slot(pmd, n, &block);
                ASSERT_MSG(r == 0, "directory_get_slot");
                r = directory_unlink_block(pmd, n);
                ASSERT_MSG(r == 0, "directory_unlink_block");
                r = free_block(block);
                ASSERT_MSG(r == 0, "free_block");
        }
        return 0;
}

void *map_block(uintptr_t va, usymlink_t block, pteval_t perm)
{
        size_t i;
        long r;
        usymlink_t pmd;

        if (va == 0) {
                ASSERT_MSG(page_walk(MMAP_START, &pmd) == 0, "page_walk");

                usymlink_t xx;
                for (i = 0; i < DIRECTORY_NR_ENTRIES; i++) {
                        if (directory_get_slot(pmd, i, &xx) != 0) {
                                va = MMAP_START + (SZ_2M * i);
                                break;
                        }
                }
        } else {
                r = page_walk(va, &pmd);
                ASSERT_MSG(r == 0, "page_walk");
                if (r != 0)
                        return 0;
        }

        ASSERT_MSG(va != 0, "unsupported");
        r = directory_link_block(pmd, pmd_index(va), block, perm);
        ASSERT_MSG(r == 0, "directory_unlink_block");
        if (r != 0)
                return 0;
        return (void*)va;
}

long unmap_block(uintptr_t va)
{
        long r;
        usymlink_t pmd;
        r = page_walk(va, &pmd);
        ASSERT_MSG(r == 0, "page_walk");
        if (r != 0)
                return r;
        r = directory_unlink_block(pmd, pmd_index(va));
        ASSERT_MSG(r == 0, "directory_unlink_block");
        return r;
}
