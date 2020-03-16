#pragma once

#include <sys/types.h>
#include <stdint.h>

#define LABEL_NR_TAGS          1024
#define CONTAINER_NR_PAGES     2048
#define PAGE_NAME_LEN          32
#define PAGE_METADATA_LEN      96
#define PGTABLE_NR_PTES        512
#define DIRECTORY_NR_ENTRIES   PGTABLE_NR_PTES
#define SCHED_NR_QUANTA        256

enum {
        PAGE_TYPE_NONE = 0,
        PAGE_TYPE_UNTYPED,
        PAGE_TYPE_LABEL,
        PAGE_TYPE_CONTAINER,
        PAGE_TYPE_PGD,
        PAGE_TYPE_PUD,
        PAGE_TYPE_PMD,
        PAGE_TYPE_GATE,
        PAGE_TYPE_THREAD,
        PAGE_TYPE_BLOCK,
        PAGE_TYPE_RESERVED = UINT64_MAX,
};

enum thread_state {
        THREAD_STATE_NONE = 0,
        THREAD_STATE_RUNNABLE,
        THREAD_STATE_HALTED,
        THREAD_STATE_MAX = UINT64_MAX,
};

typedef uint64_t        pteval_t;

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

