#pragma once

#include <asm/ptrace.h>

#include "config.h"
#include "types.h"

enum page_type {
        PAGE_FREE = 0,
        PAGE_ENCLAVE,
        PAGE_THREAD,
        PAGE_PML4,
        PAGE_PDPT,
        PAGE_PD,
        PAGE_PT,
        PAGE_FRAME,
        PAGE_VA,
        PAGE_SPARE,
        PAGE_TYPE_FORCE_WIDTH = UINT64_C(0xffffffffffffffff),
};

struct page_desc {
        pageid_t owner;
        uint64_t type;
        uint64_t address;
} __packed;

/*
 * Enclave control structure
 */
struct enclave {
        pageid_t pml4;
        size_t nr_running_threads;      /* tcs.stage is 1 */
        size_t nr_pages;
        bool64_t sealed;
        bool64_t stopped;
} __packed;

struct thread {
        uint64_t entry;
        bool64_t entered;
        struct pt_regs regs;
} __packed;
