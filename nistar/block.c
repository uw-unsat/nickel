#include <asm/e820.h>
#include <sys/errno.h>
#include <sys/multiboot.h>
#include <sys/string.h>

#include "block.h"
#include "container.h"

static struct page2m page2ms[NR_PAGE2M];

#ifdef __IRPY__
static uint64_t page2ms_data[NR_PAGE2M][PAGE2M_SIZE / sizeof(uint64_t)] __aligned(PAGE2M_SIZE);
#else
static uint64_t (*page2ms_data)[NR_PAGE2M][PAGE2M_SIZE / sizeof(uint64_t)] __aligned(PAGE2M_SIZE);
#endif

static int __page2m_alloc(struct page2m *page2m)
{
        BUG_ON(!page2m->available);
        page2m->available = false;
        return 0;
}

static void __page2m_free(struct page2m *page2m)
{
        page2m->available = true;
}

bool page2m_is_valid(page2m_id_t uid)
{
        return page2m_id_val(uid) < NR_PAGE2M;
}

struct page2m *page2m_get(page2m_id_t uid)
{
        BUG_ON(!page2m_is_valid(uid));
        return &page2ms[page2m_id_val(uid)];
}

static void *page2m_data(page2m_id_t uid)
{
        BUG_ON(!page2m_is_valid(uid));
#ifdef __IRPY__
        return &page2ms_data[page2m_id_val(uid)];
#else
        return (*page2ms_data)[page2m_id_val(uid)];
#endif
}

bool page2m_is_free(page2m_id_t uid)
{
        BUG_ON(!page2m_is_valid(uid));
        return page2m_get(uid)->available;
}

static int page2m_alloc(page2m_id_t uid)
{
        int r;
        r = __page2m_alloc(page2m_get(uid));
        if (r == 0)
                memset(page2m_data(uid), 0, SZ_2M);
        return r;
}

static void page2m_free(page2m_id_t uid)
{
        __page2m_free(page2m_get(uid));
}

static pfn_t page2m_to_pfn(page2m_id_t uid)
{
        return __pa(page2m_data(uid)) / PAGE_SIZE;
}

/* block */

void *block_data(page_id_t id)
{
        BUG_ON(!page_is_type(id, PAGE_TYPE_BLOCK));
        struct block *blk = page_data(id);
        BUG_ON(!page2m_is_valid(blk->page));
        BUG_ON(page2m_get(blk->page)->available);
        return page2m_data(blk->page);
}

pfn_t block_to_pfn(page_id_t id)
{
        BUG_ON(!page_is_type(id, PAGE_TYPE_BLOCK));
        struct block *blk = page_data(id);
        BUG_ON(!page2m_is_valid(blk->page));
        BUG_ON(page2m_get(blk->page)->available);
        return page2m_to_pfn(blk->page);
}

int untyped_to_block(page_id_t id, page2m_id_t uid)
{
        int r;
        struct block *blk;
        struct page *page;
        struct page2m *page2m;

        if (!page_is_type(id, PAGE_TYPE_UNTYPED))
                return -EINVAL;

        page = page_get(id);

        page2m = page2m_get(uid);
        if (!page2m->available)
                return -EINVAL;

        r = page2m_alloc(uid);
        if (r)
                return r;

        page->type = PAGE_TYPE_BLOCK;

        blk = page_data(id);
        blk->page = uid;
        return 0;
}

int block_alloc(page_id_t id, page2m_id_t page2m)
{
        int r;
        r = page_alloc(id, PAGE_TYPE_UNTYPED);
        if (r)
                return r;
        return untyped_to_block(id, page2m);
}

int block_free(page_id_t cid, page_id_t id)
{
        struct block *blk;
        BUG_ON(!page_is_type(id, PAGE_TYPE_BLOCK));

        blk = page_data(id);

        container_page_free(cid, page_get(id)->secrecy);
        container_page_free(cid, page_get(id)->integrity);

        page2m_free(blk->page);
        container_push_page2m(cid, blk->page);

        container_page_free(cid, id);

        return 0;
}

void block_init(page_id_t id)
{
        page2m_id_t head = PAGE2M_INVALID, next = PAGE2M_INVALID;

        uint64_t p, uquota = 0;
        for(p = 0; p < NR_PAGE2M; p++) {
                if (!page2m_is_free(__page2m_id(p))) {
                        page2m_get(__page2m_id(p))->next = PAGE2M_INVALID;
                        continue;
                }
                uquota++;
                if (safe_equal(page2m_id, head, PAGE2M_INVALID)) {
                        head = __page2m_id(p);
                        next = __page2m_id(p);
                } else {
                        page2m_get(next)->next = __page2m_id(p);
                        next = __page2m_id(p);
                        page2m_get(next)->next = PAGE2M_INVALID;
                }
        }

        page_get(id)->ufreelist_next = head;
        page_get(id)->c_uquota = uquota;
}

void block_multiboot_init(void *start)
{
        size_t i;
        phys_addr_t addr;


#ifndef __IRPY__
        page2ms_data = start;
#endif
        pr_info("page2ms [mem 0x%016" PRIx64 "-0x%016" PRIx64 "]\n",
                __pa(page2ms_data), __pa((*page2ms_data)+ NR_PAGE2M) - 1);
        for (i = 0; i < NR_PAGE2M; ++i) {
                addr = __pa(page2m_data(__page2m_id(i)));
                if (!e820_mapped_all(addr, addr + PAGE2M_SIZE, E820_TYPE_RAM)) {
                        page2m_get(__page2m_id(i))->available = false;
                        pr_info("page2m %zu reserved\n", i);
                } else {
                        page2m_get(__page2m_id(i))->available = true;
                }
        }
}
