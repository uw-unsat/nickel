#pragma once

#include <sys/types.h>
#include "mm.h"

#define NR_PAGE2M          512
#define PAGE2M_SIZE        SZ_2M
#define PAGE2M_INVALID     __page2m_id(UINT64_MAX)

struct block {
        page2m_id_t page;
};

/* page2m definitions */
struct page2m {
        bool available;
        page2m_id_t next;
};

struct page2m *page2m_get(page2m_id_t uid);
bool page2m_is_valid(page2m_id_t uid);
bool page2m_is_free(page2m_id_t uid);
page2m_id_t page2m_next_free();

/* block */
void *block_data(page_id_t uid);
pfn_t block_to_pfn(page_id_t id);

int untyped_to_block(page_id_t id, page2m_id_t uid);
int block_alloc(page_id_t id, page2m_id_t uid);
int block_free(page_id_t cid, page_id_t id);

void block_init(page_id_t id);
void block_multiboot_init(void *start);
