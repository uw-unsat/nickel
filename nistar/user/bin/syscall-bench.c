#include <stdio.h>
#include <nistar/env.h>
#include <nistar/ulib.h>

#define NR_ITER 50000

static inline void native_cpuid(unsigned int *eax, unsigned int *ebx,
                                unsigned int *ecx, unsigned int *edx)
{
        asm volatile("cpuid"
            : "=a" (*eax),
              "=b" (*ebx),
              "=c" (*ecx),
              "=d" (*edx)
            : "0" (*eax), "2" (*ecx)
            : "memory");
}

static inline void cpuid(unsigned int op,
                         unsigned int *eax, unsigned int *ebx,
                         unsigned int *ecx, unsigned int *edx)
{
        *eax = op;
        *ecx = 0;
        native_cpuid(eax, ebx, ecx, edx);
}

static inline unsigned int cpuid_eax(unsigned int op)
{
        unsigned int eax, ebx, ecx, edx;

        cpuid(op, &eax, &ebx, &ecx, &edx);

        return eax;
}

static inline uint64_t rdtsc(void)
{
        uint64_t low, high;

        asm volatile("rdtscp" : "=a" (low), "=d" (high));
        cpuid_eax(0);

        return low | (high << 32);
}

int main(void)
{
        uint64_t begin, end;
        upage_id_t root;

        begin = rdtsc();

        for (unsigned long i = 0; i < NR_ITER; ++i)
                sys_container_get_root(&root);

        end = rdtsc();

        printf("BEGIN: %lu\nEND: %lu\nCYCLES: %lu\nITERATIONS: %lu\nAVG: %lu cycles/iter\n",
              begin,
              end,
              end - begin,
              NR_ITER,
              (end - begin) / NR_ITER);

         return 0;
}
