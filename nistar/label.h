#pragma once

#include "mm.h"

#define TAG_INVALID             __tag((unsigned __int128)UINT64_MAX << 64 | UINT64_MAX)

#define LABEL_EMPTY             PAGE_ID_INVALID

/* tag_t and friends */
DEFINE_SAFE_TYPE(tag, unsigned __int128);

struct label {
        tag_t tags[LABEL_NR_TAGS];
};

static inline bool tag_is_valid(tag_t tag)
{
        return tag_val(tag) != tag_val(TAG_INVALID);
}

void tag_init(void);
tag_t tag_alloc(void);

struct label *get_label(page_id_t id);
void set_label(page_id_t id, struct label *new);
int untyped_to_label(page_id_t id);
int label_alloc(page_id_t id);
int label_add(page_id_t id, size_t slot, tag_t tag);

struct label *make_label(uint64_t *buf);

bool label_has(struct label *la, tag_t tag);
bool label_is_subset(struct label *la, struct label *lb);
bool label_is_subsetx(struct label *la, struct label *lb, struct label *lx);

bool labelp_has(page_id_t id, tag_t tag);
bool labelp_is_subset(page_id_t a, page_id_t b);
bool labelp_is_subsetx(page_id_t a, page_id_t b, page_id_t x);
