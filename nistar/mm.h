#pragma once

#include <io/mmu.h>
#include <sys/types.h>
#include <uapi/nistar/types.h>

#define PAGE_DATA_SIZE         (PAGE_SIZE * 4)
#define NR_PAGES               8192
#define PAGE_ID_INVALID        __page_id(UINT64_MAX)
#define KPAGE_ID_INVALID       ((kpage_id_t) { .id = PAGE_ID_INVALID, .generation = 0 })
#define GENERATION_MAX         UINT64_MAX

/* page_id_t and friends */
DEFINE_SAFE_TYPE(page_id, uint64_t);
DEFINE_SAFE_TYPE(page2m_id, uint64_t);
DEFINE_SAFE_TYPE(quantum_id, uint64_t);

/* unique names for kernel objects */
typedef struct {
        page_id_t id;
        uint64_t generation;
} kpage_id_t;

typedef struct {
        kpage_id_t page;
        kpage_id_t parent;
} ksymlink_t;

/* user-space names for kernel objects */

DEFINE_SAFE_TYPE(upage_id, unsigned __int128);

typedef struct {
        upage_id_t upage;
        upage_id_t uparent;
} usymlink_t;

void usymlink_init(void);

struct page {
        uint64_t generation;
        uint64_t type;
        page_id_t secrecy;
        page_id_t integrity;

        /* used for debugging */
        uint64_t name[PAGE_NAME_LEN / sizeof(uint64_t)];

        page_id_t c_parent;
        size_t c_parent_slot;

        uint64_t tag_counter;

        /* metadata for use by userspace */
        uint64_t metadata[PAGE_METADATA_LEN / sizeof(uint64_t)];

        union {
                /* container */
                struct {
                        /* Number of children in a container */
                        uint64_t c_children;

                        page_id_t freelist_next;
                        uint64_t c_quota;

                        page2m_id_t ufreelist_next;
                        uint64_t c_uquota;

                        uint64_t c_qquota;
                };
        };
};

int page_alloc(page_id_t id, uint64_t type);
struct page *page_get(page_id_t id) __pure;
void *page_data(page_id_t id) __pure;
void page_free(page_id_t id);
pfn_t page_to_pfn(page_id_t id) __pure;
page_id_t pfn_to_page(pfn_t) __pure;

static inline bool quantum_is_valid(quantum_id_t qid)
{
        return quantum_id_val(qid) < SCHED_NR_QUANTA;
}

static inline bool page_is_valid(page_id_t id)
{
        return page_id_val(id) < NR_PAGES;
}

static inline bool page_is_type(page_id_t id, uint64_t type)
{
        return page_is_valid(id) && page_get(id)->type == type;
}

static inline kpage_id_t __kpage_id(page_id_t id)
{
        return (kpage_id_t) {
                .id             = id,
                .generation     = page_get(id)->generation,
        };
}

static inline ksymlink_t __ksymlink(kpage_id_t page, kpage_id_t parent)
{
        return (ksymlink_t) {
                .page = page,
                .parent = parent
        };
}

bool ksymlink_is_valid(ksymlink_t sym);

static inline bool kpage_is_valid(kpage_id_t sym)
{
        return page_is_valid(sym.id) && page_get(sym.id)->generation == sym.generation;
}

static inline bool kpage_is_type(kpage_id_t sym, uint64_t type)
{
        if (!kpage_is_valid(sym))
                return false;
        return page_is_type(sym.id, type);
}

static inline bool ksymlink_is_viable(ksymlink_t sym)
{
    return (page_is_valid(sym.page.id) &&
            sym.page.generation > 0 &&
            page_is_valid(sym.parent.id) &&
            sym.parent.generation > 0);
}

static inline bool ksymlink_is_type(ksymlink_t sym, uint64_t type)
{
        return ksymlink_is_valid(sym) && kpage_is_type(sym.page, type);
}

void vm_init(page_id_t);

