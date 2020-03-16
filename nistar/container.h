#pragma once

#include <sys/string.h>
#include "mm.h"

struct container {
        page_id_t pages[CONTAINER_NR_PAGES];
};

extern page_id_t root_container_id;

struct container *get_container(kpage_id_t id);
int untyped_to_container(page_id_t id);
int container_alloc(page_id_t id);
long container_free(page_id_t cid, page_id_t id);

page_id_t container_pop(page_id_t id);
void container_push(page_id_t id, page_id_t subid);
void container_page_free(page_id_t id, page_id_t subid);

page2m_id_t container_pop_page2m(page_id_t id);
void container_push_page2m(page_id_t id, page2m_id_t subid);

quantum_id_t container_pop_front_quantum(page_id_t id);
void container_push_back_quantum(page_id_t id, quantum_id_t q);
void container_push_front_quantum(page_id_t id, quantum_id_t q);

int container_put_page(page_id_t id, size_t slot, page_id_t subid);
int container_set_parent(page_id_t child, page_id_t parent);
int container_reserve_page(page_id_t id, size_t slot);
size_t container_find(struct container *co, page_id_t id);
