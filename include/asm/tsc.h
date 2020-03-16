#pragma once

#include <sys/types.h>

/**
 * rdtsc() - returns the current TSC without ordering constraints
 *
 * rdtsc() returns the result of RDTSC as a 64-bit integer.  The
 * only ordering constraint it supplies is the ordering implied by
 * "asm volatile": it will put the RDTSC in the place you expect.  The
 * CPU can and will speculatively execute that RDTSC, though, so the
 * results can be non-monotonic if compared on different CPUs.
 */
static __always_inline uint64_t rdtsc(void)
{
        uint64_t low, high;

        asm volatile("rdtsc" : "=a" (low), "=d" (high));

        return low | (high << 32);
}

static __always_inline uint64_t rdtscp(void)
{
        uint64_t low, high;

        asm volatile("rdtscp" : "=a" (low), "=d" (high));

        return low | (high << 32);
}

static inline uint64_t get_cycles(void)
{
        return rdtsc();
}

useconds_t uptime(void);
