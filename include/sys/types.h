#pragma once

#ifndef __ASSEMBLER__
#include <limits.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stddef.h>
#include <io/sizes.h>
#include <sys/bug.h>
#include <sys/byteorder.h>
#include <sys/printk.h>
#include <sys/safe.h>

/**
 * container_of - cast a member of a structure out to the containing structure
 * @ptr:        the pointer to the member.
 * @type:       the type of the container struct this is embedded in.
 * @member:     the name of the member within the struct.
 *
 */
#define container_of(ptr, type, member) ({                      \
        const typeof( ((type *)0)->member ) *__mptr = (ptr);    \
        (type *)( (char *)__mptr - offsetof(type,member) );})

/* &a[0] degrades to a pointer: a different type from an array */
#define __must_be_array(a)      BUILD_BUG_ON_ZERO(__same_type((a), &(a)[0]))

#define ARRAY_SIZE(arr) (sizeof(arr) / sizeof((arr)[0]) + __must_be_array(arr))

/*
 * min()/max()/clamp() macros that also do
 * strict type-checking.. See the
 * "unnecessary" pointer comparison.
 */
#define __min(t1, t2, min1, min2, x, y) ({              \
        t1 min1 = (x);                                  \
        t2 min2 = (y);                                  \
        (void) (&min1 == &min2);                        \
        min1 < min2 ? min1 : min2; })

/**
 * min - return minimum of two values of the same or compatible types
 * @x: first value
 * @y: second value
 */
#define min(x, y)                                       \
        __min(typeof(x), typeof(y),                     \
              __UNIQUE_ID(min1_), __UNIQUE_ID(min2_),   \
              x, y)

#define __max(t1, t2, max1, max2, x, y) ({              \
        t1 max1 = (x);                                  \
        t2 max2 = (y);                                  \
        (void) (&max1 == &max2);                        \
        max1 > max2 ? max1 : max2; })

/**
 * max - return maximum of two values of the same or compatible types
 * @x: first value
 * @y: second value
 */
#define max(x, y)                                       \
        __max(typeof(x), typeof(y),                     \
              __UNIQUE_ID(max1_), __UNIQUE_ID(max2_),   \
              x, y)

/**
 * min_t - return minimum of two values, using the specified type
 * @type: data type to use
 * @x: first value
 * @y: second value
 */
#define min_t(type, x, y)                               \
        __min(type, type,                               \
              __UNIQUE_ID(min1_), __UNIQUE_ID(min2_),   \
              x, y)

/**
 * max_t - return maximum of two values, using the specified type
 * @type: data type to use
 * @x: first value
 * @y: second value
 */
#define max_t(type, x, y)                               \
        __max(type, type,                               \
              __UNIQUE_ID(min1_), __UNIQUE_ID(min2_),   \
              x, y)

#define do_div(n, base) ({                      \
        uint32_t __base = (base);               \
        uint32_t __rem;                         \
        __rem = ((uint64_t)(n)) % __base;       \
        (n) = ((uint64_t)(n)) / __base;         \
        __rem;                                  \
 })

#define roundup(x, y) (                                 \
{                                                       \
        const typeof(y) __y = y;                        \
        (((x) + (__y - 1)) / __y) * __y;                \
}                                                       \
)

#define rounddown(x, y) (                               \
{                                                       \
        typeof(x) __x = (x);                            \
        __x - (__x % (y));                              \
}                                                       \
)

#define ALIGN(x, a)             __ALIGN_MASK(x, (typeof(x))(a) - 1)
#define __ALIGN_MASK(x, mask)   (((x) + (mask)) & ~(mask))
#define PTR_ALIGN(p, a)         ((typeof(p))ALIGN((uintptr_t)(p), (a)))

#define BITS_PER_BYTE           8
#define BITS_PER_LONG           (BITS_PER_BYTE * __SIZEOF_LONG__)

#define DIV_ROUND_UP(n, d)      (((n) + (d) - 1) / (d))
#define BITS_TO_LONGS(nr)       DIV_ROUND_UP(nr, BITS_PER_BYTE * sizeof(long))

#define DECLARE_BITMAP(name,bits) unsigned long name[BITS_TO_LONGS(bits)]

typedef uint64_t        pfn_t;
typedef uint64_t        phys_addr_t;
typedef phys_addr_t     resource_size_t;
typedef uint64_t        pteval_t;
typedef intmax_t        ssize_t;
typedef uint64_t        useconds_t;

struct list_head {
        struct list_head *next, *prev;
};

extern char _start[], _end[], __entry_text_start[], __entry_text_end[];

/* Always use identity mapping */

static inline void *__va(phys_addr_t pa)
{
        return (void *)pa;
}

static inline phys_addr_t __pa(void *va)
{
        return (uintptr_t)va;
}

extern const char hex_asc[];
#define hex_asc_lo(x)   hex_asc[((x) & 0x0f)]
#define hex_asc_hi(x)   hex_asc[((x) & 0xf0) >> 4]

static inline char *hex_byte_pack(char *buf, uint8_t byte)
{
        *buf++ = hex_asc_hi(byte);
        *buf++ = hex_asc_lo(byte);
        return buf;
}

extern const char hex_asc_upper[];
#define hex_asc_upper_lo(x)     hex_asc_upper[((x) & 0x0f)]
#define hex_asc_upper_hi(x)     hex_asc_upper[((x) & 0xf0) >> 4]

static inline char *hex_byte_pack_upper(char *buf, uint8_t byte)
{
        *buf++ = hex_asc_upper_hi(byte);
        *buf++ = hex_asc_upper_lo(byte);
        return buf;
}

int hex_to_bin(char ch);
int __must_check hex2bin(uint8_t *dst, const char *src, size_t count);
extern char *bin2hex(char *dst, const void *src, size_t count);

#endif  /* !__ASSEMBLER__ */
