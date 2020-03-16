#pragma once

#include "mm.h"

#define GATE_NR_ARGS 6

struct gate {
        page_id_t   ownership;
        page_id_t   guard;
        ksymlink_t  mm;
        uintptr_t   entry;
        uint64_t    args[GATE_NR_ARGS];
};


struct gate *get_gate(page_id_t id);
int untyped_to_gate(page_id_t id);
int gate_free(page_id_t cid, page_id_t id);
