#include <stdio.h>
#include <nistar/env.h>
#include <nistar/ulib.h>

#define NR_ITER 1000

static uint64_t timestamps[NR_ITER];

static __always_inline uint64_t rdtsc(void)
{
        uint64_t low, high;

        asm volatile("rdtsc" : "=a" (low), "=d" (high));

        return low | (high << 32);
}

static inline void sleep(uint64_t cycles)
{
        uint64_t start = rdtsc();
        while (rdtsc() - start < cycles)
            ;
}

int main(void)
{
        unsigned long i = 0;
        unsigned long prev = sys_debug_elapsed_quanta();

        while (i < NR_ITER) {
                unsigned long next = sys_debug_elapsed_quanta();
                if (next == prev)
                        continue;
                timestamps[i++] = next;
                prev = next;
        }

        for (unsigned long i = 1; i < NR_ITER; ++i)
                printf("TIMER %lu %lu %lu\n", i,
                    timestamps[i],
                    timestamps[i] - timestamps[i-1]);

        return 0;
}
