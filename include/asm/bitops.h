#pragma once

#include <sys/types.h>

#if BITS_PER_LONG == 32
# define _BITOPS_LONG_SHIFT 5
#elif BITS_PER_LONG == 64
# define _BITOPS_LONG_SHIFT 6
#else
# error "Unexpected BITS_PER_LONG"
#endif

#define BITOP_ADDR(x) "+m" (*(volatile long *) (x))

static __always_inline void set_bit(long nr, volatile unsigned long *addr)
{
        asm volatile("bts %1,%0" : BITOP_ADDR(addr) : "Ir" (nr) : "memory");
}

static __always_inline void clear_bit(long nr, volatile unsigned long *addr)
{
        asm volatile("btr %1,%0" : BITOP_ADDR(addr) : "Ir" (nr));
}

static __always_inline bool constant_test_bit(long nr, const volatile unsigned long *addr)
{
        return ((1UL << (nr & (BITS_PER_LONG-1))) &
                (addr[nr >> _BITOPS_LONG_SHIFT])) != 0;
}

static __always_inline bool variable_test_bit(long nr, volatile const unsigned long *addr)
{
        bool oldbit;

        asm volatile("bt %2,%1\n\t"
                     CC_SET(c)
                     : CC_OUT(c) (oldbit)
                     : "m" (*(unsigned long *)addr), "Ir" (nr));

        return oldbit;
}

#define test_bit(nr, addr)                      \
        (__builtin_constant_p((nr))             \
         ? constant_test_bit((nr), (addr))      \
         : variable_test_bit((nr), (addr)))

/**
 * __ffs - find first set bit in word
 * @word: The word to search
 *
 * Undefined if no bit exists, so code should check against 0 first.
 */
static __always_inline unsigned long __ffs(unsigned long word)
{
        asm("rep; bsf %1,%0"
                : "=r" (word)
                : "rm" (word));
        return word;
}

/**
 * ffz - find first zero bit in word
 * @word: The word to search
 *
 * Undefined if no zero exists, so code should check against ~0UL first.
 */
static __always_inline unsigned long ffz(unsigned long word)
{
        asm("rep; bsf %1,%0"
                : "=r" (word)
                : "r" (~word));
        return word;
}

/*
 * __fls: find last set bit in word
 * @word: The word to search
 *
 * Undefined if no set bit exists, so code should check against 0 first.
 */
static __always_inline unsigned long __fls(unsigned long word)
{
        asm("bsr %1,%0"
            : "=r" (word)
            : "rm" (word));
        return word;
}
