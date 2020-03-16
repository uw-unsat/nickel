#include <stdio.h>
#include <nistar/env.h>
#include <nistar/ulib.h>

#define NR_ITER 5000

static uint64_t timestamps[NR_ITER];

static __always_inline uint64_t rdtsc(void)
{
        uint64_t low, high;

        asm volatile("rdtsc" : "=a" (low), "=d" (high));

        return low | (high << 32);
}

int main(void)
{
        for (unsigned long i = 0; i < NR_ITER; ++i)
                timestamps[i] = rdtsc();

        for (unsigned long i = 0; i < NR_ITER; ++i)
                printf("TIMER %lu %lu\n", i, timestamps[i]);

        return 0;
}
