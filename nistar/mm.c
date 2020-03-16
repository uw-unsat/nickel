#define pr_fmt(fmt) __MODULE__ ": " fmt

#include <asm/setup.h>
#include <sys/errno.h>
#include <sys/ilist.h>
#include <sys/multiboot.h>
#include <sys/string.h>
#include "assume.h"
#include "mm.h"
#include "block.h"
#include "container.h"
#include "label.h"

phys_addr_t initrd_start, initrd_end;
char cmdline[CMDLINE_SIZE];

static struct page pages[NR_PAGES];

#ifdef __IRPY__
static uint64_t pages_data[NR_PAGES][PAGE_DATA_SIZE / sizeof(uint64_t)] __aligned(PAGE_SIZE);
#else
static uint64_t (*pages_data)[NR_PAGES][PAGE_DATA_SIZE / sizeof(uint64_t)] __aligned(PAGE_SIZE);
#endif

static int __page_alloc(struct page *page, uint64_t type)
{
        BUG_ON(type == PAGE_TYPE_NONE);

        /* must be a free page */
        if (page->type != PAGE_TYPE_NONE)
                return -EINVAL;

        ++page->generation;
        page->type = type;

        memset64(page->name, 0, sizeof(page->name) / sizeof(uint64_t));
        memset64(page->metadata, 0, sizeof(page->metadata) / sizeof(uint64_t));

        page->secrecy = LABEL_EMPTY;
        page->integrity = LABEL_EMPTY;

        page->c_quota = 0;
        page->freelist_next = PAGE_ID_INVALID;

        return 0;
}

void __page_free(struct page *page)
{
        BUG_ON(page->type == PAGE_TYPE_NONE);

        page->type = PAGE_TYPE_NONE;
}

/* kernel pages */

int page_alloc(page_id_t id, uint64_t type)
{
        long r;
        r = __page_alloc(page_get(id), type);
        if (r == 0)
                memset(page_data(id), 0, PAGE_DATA_SIZE);
        return r;

}

struct page *page_get(page_id_t id)
{
        BUG_ON(!page_is_valid(id));
        return &pages[page_id_val(id)];
}

void *page_data(page_id_t id)
{
        BUG_ON(!page_is_valid(id));

#ifdef __IRPY__
        return &pages_data[page_id_val(id)];
#else
        return (*pages_data)[page_id_val(id)];
#endif
}

void page_free(page_id_t id)
{
        return __page_free(page_get(id));
}

pfn_t page_to_pfn(page_id_t id)
{
        return __pa(page_data(id)) / PAGE_DATA_SIZE;
}

page_id_t pfn_to_page(pfn_t pfn)
{
        return __page_id((pfn * PAGE_DATA_SIZE - __pa(page_data(__page_id(0)))) / PAGE_DATA_SIZE);
}

bool ksymlink_is_valid(ksymlink_t sym)
{
        /* page is a valid reference */
        if (!kpage_is_valid(sym.page))
                return false;

        /* the parent is a valid container reference */
        if (!kpage_is_type(sym.parent, PAGE_TYPE_CONTAINER))
                return false;

        /* the object appears in the parent container */
        return safe_equal(page_id, page_get(sym.page.id)->c_parent, sym.parent.id);
}

void vm_init(page_id_t root_container)
{
        page_id_t head = root_container;
        uint64_t quota = 0;
        uint64_t p;
        for(p = 0; p < NR_PAGES; p++) {
                if (page_get(__page_id(p))->type == PAGE_TYPE_NONE) {
                        page_get(head)->freelist_next = __page_id(p);
                        quota++;
                        head = __page_id(p);
                } else {
                        page_get(__page_id(p))->freelist_next = PAGE_ID_INVALID;
                }
        }
        page_get(root_container)->c_quota = quota;
}

void multiboot_init(uint32_t magic, struct multiboot_info *info)
{
        struct multiboot_mod_list *mod;
        size_t i;
        phys_addr_t addr;

        BUG_ON(magic != MULTIBOOT_BOOTLOADER_MAGIC);
        BUG_ON(!info);

        e820_range_add_multiboot(__va(info->mmap_addr), info->mmap_length);

        BUG_ON(!e820_mapped_all(__pa(_start), __pa(_end), E820_TYPE_RAM));
        e820_range_update(__pa(_start), _end - _start, E820_TYPE_RAM, E820_TYPE_RESERVED);

        if (!(info->flags & MULTIBOOT_INFO_MODS) || !info->mods_count)
                panic("initrd required!\n");

        mod = __va(info->mods_addr);
        initrd_start = mod->mod_start;
        initrd_end = mod->mod_end;
        /* reserve space of initrd */
        e820_range_update(initrd_start, initrd_end - initrd_start, E820_TYPE_RAM, E820_TYPE_RESERVED);

        if (info->flags & MULTIBOOT_INFO_CMDLINE)
                strscpy(cmdline, __va(info->cmdline), sizeof(cmdline));

        /* don't touch multiboot after this point */

        /* pages start after the kernel/initrd */

#ifndef __IRPY__
        pages_data = __va(roundup(max(__pa(_end), initrd_end), PAGE_SIZE));
#endif
        pr_info("pages [mem 0x%016" PRIx64 "-0x%016" PRIx64 "]\n",
                __pa(pages_data), __pa((*pages_data) + NR_PAGES) - 1);
        for (i = 0; i < NR_PAGES; ++i) {
                addr = __pa(page_data(__page_id(i)));
                if (!e820_mapped_all(addr, addr + PAGE_DATA_SIZE, E820_TYPE_RAM)) {
                        page_get(__page_id(i))->type = PAGE_TYPE_RESERVED;
                        pr_info("page %zu reserved\n", i);
                }
        }

        /* upages start after kpages */
        block_multiboot_init(__va(roundup(__pa((*pages_data) + NR_PAGES), PAGE2M_SIZE)));
}
