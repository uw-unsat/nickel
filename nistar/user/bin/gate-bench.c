#include <stdio.h>
#include <nistar/env.h>
#include <nistar/ulib.h>

#define NR_ITER 5000

static __always_inline uint64_t rdtsc(void)
{
        uint64_t low, high;

        asm volatile("rdtsc" : "=a" (low), "=d" (high));

        return low | (high << 32);
}

long gate_test(uint64_t arg0, uint64_t arg1)
{
        return 1339;
}

int main(void)
{
        uint64_t begin, end;
        usymlink_t gate;
        struct label secrecy;
        struct label integrity;
        struct label ownership;
        struct label guard;
        usymlink_t internal;
        self_get_label(&secrecy, &integrity, &ownership);
        label_init(&guard);

        internal = self_get_internal_container();

        alloc_call_gate(&gate, self_get_internal_container(), &secrecy, &integrity,
                        &ownership, &guard, self_get_pud(), gate_test, 1337, "test");

        begin = rdtsc();

        for (unsigned long i = 0; i < NR_ITER; ++i)
                gate_call(gate, internal, 1338);

        end = rdtsc();

        printf("BEGIN: %lu\nEND: %lu\nCYCLES: %lu\nITERATIONS: %lu\nAVG: %lu cycles/iter\n",
              begin,
              end,
              end - begin,
              NR_ITER,
              (end - begin) / NR_ITER);

         return 0;
}
