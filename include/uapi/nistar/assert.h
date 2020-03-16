#pragma once

#include <stdnoreturn.h>

#define ASSERT_MSG(exp, fmt, ...)                                                                  \
({                                                                                             \
    if (!(exp))                                                                                \
        panic("%s:%d: %s: assert failed: " fmt, __FILE__, __LINE__, __func__, ##__VA_ARGS__);  \
})

#define ASSERT(exp)                                                                  \
({                                                                                             \
        ASSERT_MSG(exp, ""); \
})

noreturn void panic(const char *fmt, ...);
