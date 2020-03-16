#include <sys/errno.h>
#include <sys/string.h>

#include "gate.h"
#include "container.h"

struct gate *get_gate(page_id_t id)
{
        BUG_ON(!page_is_type(id, PAGE_TYPE_GATE));
        return page_data(id);
}

int untyped_to_gate(page_id_t id)
{
        struct page *page;
        struct gate *gate;

        if (!page_is_type(id, PAGE_TYPE_UNTYPED))
                return -EINVAL;

        page = page_get(id);
        page->type = PAGE_TYPE_GATE;
        gate = get_gate(id);
        gate->ownership = PAGE_ID_INVALID;
        gate->entry = 0;
        gate->args[0] = 0;
        gate->args[1] = 0;
        gate->args[2] = 0;
        gate->args[3] = 0;
        gate->args[4] = 0;
        gate->args[5] = 0;
        return 0;
}

int gate_free(page_id_t cid, page_id_t id)
{
        struct gate *gate;
        BUG_ON(!page_is_type(id, PAGE_TYPE_GATE));

        gate = page_data(id);
        container_page_free(cid, gate->ownership);
        container_page_free(cid, gate->guard);
        container_page_free(cid, page_get(id)->secrecy);
        container_page_free(cid, page_get(id)->integrity);
        container_page_free(cid, id);

        return 0;
}
