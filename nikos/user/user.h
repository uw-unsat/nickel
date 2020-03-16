#pragma once

#include <io/sizes.h>
#include <mcertikos/elf.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#define max(a, b)                                                                                  \
    ({                                                                                             \
        _Static_assert(__builtin_types_compatible_p(typeof(a), typeof(b)),                         \
                      "must be the same type");                                                    \
        typeof(a) _a = (a);                                                                        \
        typeof(b) _b = (b);                                                                        \
        _a >= _b ? _a : _b;                                                                        \
    })

/* syscalls */
long get_quota(void);
long spawn(size_t fileid, size_t quota);
void yield(void);
void print(unsigned char c);

/* libc functions */
void printf(const char *fmt, ...);
size_t strlen(const char *s);
