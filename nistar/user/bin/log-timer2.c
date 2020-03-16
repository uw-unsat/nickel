#include <stdio.h>
#include <nistar/env.h>
#include <nistar/ulib.h>
#include <unistd.h>

#define NR_POINTS 100

static inline void native_cpuid(unsigned int *eax, unsigned int *ebx,
                                unsigned int *ecx, unsigned int *edx)
{
        /* ecx is often an input as well as an output. */
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

static __always_inline uint64_t rdtsc(void)
{
        uint64_t low, high;

        asm volatile("rdtscp" : "=a" (low), "=d" (high));
        cpuid_eax(0);

        return low | (high << 32);
}

uint64_t calibrate(uint64_t baseline) {
        uint64_t now, last, max = 0;
        for (int i = 0; i < NR_POINTS; i++) {
                last = rdtsc();
                now = rdtsc();
                if (now - last > max)
                        max = now - last;
        }
        return max;
}

uint64_t get_timer(uint64_t calib) {
        uint64_t now, last;
        for (int i = 0; i < 10; i++)
                rdtsc();
        while(1) {
                last = rdtsc();
                now = rdtsc();
                if (now - last > calib)
                        return now - last;
        }
}

/* uint64_t detect_spike(uint64_t baseline) { */
/*         uint64_t now, last, max = 0; */
/*         last = rdtsc(); */
/*         for (int i = 0; i < NR_POINTS; i++) { */
/*                 now = rdtsc(); */
/*                 if (now - last > max) */
/*                         max = now - last; */
/*                 last = rdtsc(); */
/*         } */
/*         return max; */
/* } */
/*  */
/* } */

/* uint64_t detect_signal(uint64_t calib, uint64_t baseline) { */
/*         uint64_t last, now; */
/*         last = avg(); */
/*         while (1) { */
/*                 now = avg(); */
/*                 if (now - last < baseline && now - last > calib) */
/*                         return now - last; */
/*                 last = now; */
/*         } */
/* } */

int main(void)
{
        /* uint64_t calib, baseline, zero, one; */
        uint64_t calib, now, last;

        calib = calibrate(0) * 50;

        debug_printf("TIMER CALIBRATION: %lu\n", calib);

        while (1) {
                for (int i = 0; i < 10; i++)
                        rdtsc();
                while(1) {
                        last = rdtsc();
                        now = rdtsc();
                        if (now - last > calib)
                                break;
                }
                debug_printf("TIMER: %lu %lu\n", now, now - last);
        }


        /* baseline = calibrate(calib * 10); */
        /* debug_printf("TIMER BASELINE: %lu\n", baseline); */

        /* usleep(10000000); */

        /* debug_printf("STARTING ZERO CALBIRATION\n"); */

        /* zero = calibrate(baseline + baseline); */

        /* debug_printf("TIMER ZERO: %lu\n", zero); */

        /* detect_signal(baseline / 2, zero / 2); */

        /* debug_printf("BASELINE DETECTED\n"); */


        //////////

        return 0;
}
