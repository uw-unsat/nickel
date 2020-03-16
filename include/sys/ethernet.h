#pragma once

#include <sys/types.h>

struct ethernet {
        size_t (*transmit)(struct ethernet *, const void *, size_t);
        size_t (*receive)(struct ethernet *, void *, size_t);
        struct list_head list;
};

void ethernet_register(struct ethernet *);
struct ethernet *ethernet_first(void);
