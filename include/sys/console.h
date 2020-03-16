#pragma once

#include <sys/types.h>

/* Colors */
#define BRIGHT_YELLOW "\x1b[33;1m"
#define BRIGHT_PURPLE "\x1b[35;1m"

struct console {
        int (*getc)(struct console *);
        void (*write)(struct console *, const char *, size_t);
        struct list_head list;
};

void register_console(struct console *);

int getchar(void);
