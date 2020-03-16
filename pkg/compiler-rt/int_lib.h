#pragma once

#include <limits.h>

#define COMPILER_RT_ABI
#define CRT_HAS_128BIT

/* Clang and GCC provide built-in endianness definitions. */
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
#define _YUGA_LITTLE_ENDIAN 0
#define _YUGA_BIG_ENDIAN    1
#elif __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
#define _YUGA_LITTLE_ENDIAN 1
#define _YUGA_BIG_ENDIAN    0
#endif /* __BYTE_ORDER__ */

typedef unsigned su_int;

typedef          long long di_int;
typedef unsigned long long du_int;

typedef int      ti_int __attribute__ ((mode (TI)));
typedef unsigned tu_int __attribute__ ((mode (TI)));

typedef union
{
    tu_int all;
    struct
    {
#if _YUGA_LITTLE_ENDIAN
        du_int low;
        du_int high;
#else
        du_int high;
        du_int low;
#endif /* _YUGA_LITTLE_ENDIAN */
    }s;
} utwords;

tu_int __udivmodti4(tu_int a, tu_int b, tu_int *rem);
