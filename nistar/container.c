#include <sys/errno.h>
#include <sys/string.h>
#include "assume.h"
#include "mm.h"
#include "container.h"
#include "block.h"
#include "sched.h"

page_id_t root_container_id;

struct container *get_container(kpage_id_t id)
{
        BUG_ON(kpage_is_type(id, PAGE_TYPE_CONTAINER));
        return page_data(id.id);
}

int untyped_to_container(page_id_t id)
{
        struct page *page;
        struct container *container;
        BUILD_BUG_ON(sizeof(struct container) != PAGE_DATA_SIZE);

        if (!page_is_type(id, PAGE_TYPE_UNTYPED))
                return -EINVAL;

        page = page_get(id);
        page->type = PAGE_TYPE_CONTAINER;
        page->c_quota = 0;
        page->c_uquota = 0;
        page->c_qquota = 0;
        page->freelist_next = PAGE_ID_INVALID;
        page->ufreelist_next = PAGE2M_INVALID;
        container = page_data(id);
        memset(page_id_ptr(container->pages), 0xff, sizeof(container->pages));
        return 0;
}

int container_alloc(page_id_t id)
{
        int r;
        r = page_alloc(id, PAGE_TYPE_UNTYPED);
        if (r)
                return r;
        return untyped_to_container(id);
}

long container_free(page_id_t cid, page_id_t id)
{
        struct page *page = page_get(id);

        if (safe_equal(page_id, cid, id))
                return -EINVAL;
        if (page->c_quota != 0)
                return -EINVAL;
        if (page->c_uquota != 0)
                return -EINVAL;
        if (page->c_qquota != 0)
                return -EINVAL;

        container_page_free(cid, page->secrecy);
        container_page_free(cid, page->integrity);
        container_page_free(cid, id);
        return 0;
}

page_id_t container_pop(page_id_t id)
{
        struct page *page = page_get(id);
        BUG_ON(page->c_quota == 0);
        page_id_t next = page->freelist_next;
        ASSUME(page_is_valid(next));
        ASSUME(page_get(next)->type == PAGE_TYPE_NONE);
        page->freelist_next = page_get(next)->freelist_next;
        page->c_quota--;
        return next;
}

void container_push(page_id_t id, page_id_t subid)
{
        struct page *container, *page;
        container = page_get(id);
        page = page_get(subid);

        BUG_ON(!page_is_type(id, PAGE_TYPE_CONTAINER));
        BUG_ON(!page_is_type(subid, PAGE_TYPE_NONE));

        page_get(subid)->c_parent = id;

        page->freelist_next = container->freelist_next;
        container->freelist_next = subid;
        container->c_quota++;
}

void container_page_free(page_id_t id, page_id_t subid)
{
        ASSUME(page_get(subid)->type != PAGE_TYPE_NONE);
        page_free(subid);
        container_push(id, subid);
}

page2m_id_t container_pop_page2m(page_id_t id)
{
        struct page *page = page_get(id);
        BUG_ON(page->c_uquota == 0);
        page2m_id_t next = page->ufreelist_next;
        ASSUME(page2m_is_valid(next));
        ASSUME(page2m_is_free(next));
        page->ufreelist_next = page2m_get(next)->next;
        page->c_uquota--;
        return next;
}

void container_push_page2m(page_id_t id, page2m_id_t subid)
{
        struct page *container;
        struct page2m *page;
        container = page_get(id);
        page = page2m_get(subid);

        BUG_ON(!page_is_type(id, PAGE_TYPE_CONTAINER));
        BUG_ON(!page2m_is_valid(subid));

        page->next = container->ufreelist_next;
        container->ufreelist_next = subid;
        container->c_uquota++;
}

int container_reserve_page(page_id_t id, size_t slot)
{
        int r;
        page_id_t subid;
        struct page *containerp;
        struct container *container;

        // DEBUG
        BUG_ON(!page_is_type(id, PAGE_TYPE_CONTAINER));

        /* arguments are valid  */
        if (!page_is_type(id, PAGE_TYPE_CONTAINER))
                return -EINVAL;
        if (!(slot < CONTAINER_NR_PAGES))
                return -EINVAL;
        containerp = page_get(id);
        /* must have enough quota */
        if (containerp->c_quota == 0)
                return -EDQUOT;
        container = page_data(id);
        /* must be a free slot */
        if (page_is_valid(container->pages[slot]))
                return -EINVAL;

        subid = container_pop(id);
        r = page_alloc(subid, PAGE_TYPE_UNTYPED);
        BUG_ON(r);

        page_get(subid)->c_parent = id;
        page_get(subid)->c_parent_slot = slot;

        container->pages[slot] = subid;
        return 0;
}

int container_put_page(page_id_t id, size_t slot, page_id_t subid)
{
        struct container *container;

        BUG_ON(!page_is_type(id, PAGE_TYPE_CONTAINER));

        if (!(slot < CONTAINER_NR_PAGES))
                return -EINVAL;

        container = page_data(id);
        /* must be a free slot */
        if (page_is_valid(container->pages[slot]))
                return -EINVAL;

        page_get(subid)->c_parent = id;
        page_get(subid)->c_parent_slot = slot;

        container->pages[slot] = subid;
        return 0;
}

int container_set_parent(page_id_t child, page_id_t parent)
{

        BUG_ON(!page_is_type(child, PAGE_TYPE_CONTAINER));
        BUG_ON(!page_is_type(parent, PAGE_TYPE_CONTAINER));
        page_get(child)->c_parent = parent;
        return 0;
}

size_t container_find(struct container *co, page_id_t id)
{
        return memfind64((uint64_t*)co->pages, page_id_val(id), CONTAINER_NR_PAGES);
}

