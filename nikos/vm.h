#pragma once

#include <sys/types.h>

struct page {
        uint64_t owner;
};

void vm_init(void);
noreturn void vm_switch(uint64_t pid);
long vm_alloc(uint64_t pid, size_t slot);
void *vm_get_data(uint64_t pageid);
