#pragma once

#include <io/compiler.h>

/* Force a compilation error if condition is true, but also produce a
   result (of value 0 and type size_t), so the expression can be used
   e.g. in a structure initializer (or where-ever else comma expressions
   aren't permitted). */
#define BUILD_BUG_ON_ZERO(e) (sizeof(struct { int:-!!(e); }))
#define BUILD_BUG_ON_NULL(e) ((void *)sizeof(struct { int:-!!(e); }))

#define BUILD_BUG_ON_MSG(cond, msg) _Static_assert(!(cond), msg)

#define BUILD_BUG_ON(condition) \
        BUILD_BUG_ON_MSG(condition, "BUILD_BUG_ON failed: " #condition)

#define BUG() do { \
        panic("BUG: failure at %s:%d/%s()\n", __FILE__, __LINE__, __func__); \
} while (0)

#define BUG_ON(condition) do { if (condition) BUG(); } while (0)

#define BUILD_BUG_ON_NOT_POWER_OF_2(n)                  \
        BUILD_BUG_ON((n) == 0 || (((n) & ((n) - 1)) != 0))

#define assert(condition) BUG_ON(!(condition))

__printf(1, 2) noreturn
void panic(const char *fmt, ...);

noreturn void die(void);

void dump_stack(void);
