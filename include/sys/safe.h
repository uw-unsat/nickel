#pragma once

#ifdef CONFIG_SAFE_TYPE

#define __DEFINE_SAFE_TYPE(name, prefix, type)                          \
typedef struct { type val; } name;                                      \
static inline name __##prefix(type val) { return (name){ val }; }       \
static inline type prefix##_val(name x) { return x.val; }               \
static inline type *prefix##_ptr(name *p) { return (type *)p; }

#else   /* !CONFIG_SAFE_TYPE */

#define __DEFINE_SAFE_TYPE(name, prefix, type)                          \
typedef type name;                                                      \
static inline name __##prefix(type val) { return val; }                 \
static inline type prefix##_val(name x) { return x; }                   \
static inline type *prefix##_ptr(name *p) { return p; }

#endif  /* CONFIG_SAFE_TYPE */

#define DEFINE_SAFE_TYPE(prefix, type)                                  \
        __DEFINE_SAFE_TYPE(prefix##_t, prefix, type)

#define safe_equal(prefix, x, y)                                        \
({                                                                      \
        prefix##_val(x) == prefix##_val(y);                             \
})
