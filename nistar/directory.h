#pragma once

#include "mm.h"

struct directory {
        ksymlink_t entries[DIRECTORY_NR_ENTRIES];
} __aligned(SZ_4K);

struct directoryf {
        uint64_t entries[DIRECTORY_NR_ENTRIES*sizeof(ksymlink_t)/sizeof(uint64_t)];
} __aligned(SZ_4K);

struct directory *get_directory(kpage_id_t id);
int untyped_to_directory(page_id_t id, uint64_t type);
int directory_alloc(page_id_t id, uint64_t type);
ksymlink_t directory_get(page_id_t id, size_t slot);
int directory_put(page_id_t id, size_t slot, ksymlink_t subid);
int directory_link(page_id_t id, size_t slot, ksymlink_t blkid, pteval_t perm);
int directory_unlink(page_id_t id, size_t slot);
int directory_free(page_id_t cid, page_id_t id);
