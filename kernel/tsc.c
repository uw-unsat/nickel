#define pr_fmt(fmt) __MODULE__ ": " fmt

#include <asm/io.h>
#include <asm/processor.h>
#include <asm/tsc.h>

static unsigned long tsc_khz;

static unsigned long native_calibrate_tsc(void)
{
        unsigned int eax_denominator, ebx_numerator, ecx_hz, edx;
        unsigned int crystal_khz;

        if (boot_cpu_data.x86_vendor != X86_VENDOR_INTEL)
                return 0;

        if (boot_cpu_data.cpuid_level < 0x15)
                return 0;

        eax_denominator = ebx_numerator = ecx_hz = edx = 0;

        /* CPUID 15H TSC/Crystal ratio, plus optionally Crystal Hz */
        cpuid(0x15, &eax_denominator, &ebx_numerator, &ecx_hz, &edx);

        if (ebx_numerator == 0 || eax_denominator == 0)
                return 0;

        crystal_khz = ecx_hz / 1000;

        if (crystal_khz == 0) {
                switch (boot_cpu_data.x86_model) {
                case INTEL_FAM6_SKYLAKE_MOBILE:
                case INTEL_FAM6_SKYLAKE_DESKTOP:
                case INTEL_FAM6_KABYLAKE_MOBILE:
                case INTEL_FAM6_KABYLAKE_DESKTOP:
                        crystal_khz = 24000;    /* 24.0 MHz */
                        break;
                case INTEL_FAM6_SKYLAKE_X:
                case INTEL_FAM6_ATOM_DENVERTON:
                        crystal_khz = 25000;    /* 25.0 MHz */
                        break;
                case INTEL_FAM6_ATOM_GOLDMONT:
                        crystal_khz = 19200;    /* 19.2 MHz */
                        break;
                }
        }

        return crystal_khz * ebx_numerator / eax_denominator;
}

/*
 * This reads the current MSB of the PIT counter, and
 * checks if we are running on sufficiently fast and
 * non-virtualized hardware.
 *
 * Our expectations are:
 *
 *  - the PIT is running at roughly 1.19MHz
 *
 *  - each IO is going to take about 1us on real hardware,
 *    but we allow it to be much faster (by a factor of 10) or
 *    _slightly_ slower (ie we allow up to a 2us read+counter
 *    update - anything else implies a unacceptably slow CPU
 *    or PIT for the fast calibration to work.
 *
 *  - with 256 PIT ticks to read the value, we have 214us to
 *    see the same MSB (and overhead like doing a single TSC
 *    read per MSB value etc).
 *
 *  - We're doing 2 reads per loop (LSB, MSB), and we expect
 *    them each to take about a microsecond on real hardware.
 *    So we expect a count value of around 100. But we'll be
 *    generous, and accept anything over 50.
 *
 *  - if the PIT is stuck, and we see *many* more reads, we
 *    return early (and the next caller of pit_expect_msb()
 *    then consider it a failure when they don't see the
 *    next expected value).
 *
 * These expectations mean that we know that we have seen the
 * transition from one expected value to another with a fairly
 * high accuracy, and we didn't miss any events. We can thus
 * use the TSC value at the transitions to calculate a pretty
 * good value for the TSC frequencty.
 */
static inline int pit_verify_msb(unsigned char val)
{
        /* Ignore LSB */
        inb(0x42);
        return inb(0x42) == val;
}

static inline int pit_expect_msb(unsigned char val, uint64_t *tscp, unsigned long *deltap)
{
        int count;
        uint64_t tsc = 0, prev_tsc = 0;

        for (count = 0; count < 50000; count++) {
                if (!pit_verify_msb(val))
                        break;
                prev_tsc = tsc;
                tsc = get_cycles();
        }
        *deltap = get_cycles() - prev_tsc;
        *tscp = tsc;

        /*
         * We require _some_ success, but the quality control
         * will be based on the error terms on the TSC values.
         */
        return count > 5;
}

/* The clock frequency of the i8253/i8254 PIT */
#define PIT_TICK_RATE                   1193182ul

/*
 * How many MSB values do we want to see? We aim for
 * a maximum error rate of 500ppm (in practice the
 * real error is much smaller), but refuse to spend
 * too much time on it (500ms is good for Bochs).
 */
#define MAX_QUICK_PIT_MS                500
#define MAX_QUICK_PIT_ITERATIONS        (MAX_QUICK_PIT_MS * PIT_TICK_RATE / 1000 / 256)

static unsigned long quick_pit_calibrate(void)
{
        int i;
        uint64_t tsc, delta;
        unsigned long d1, d2;

        /* Set the Gate high, disable speaker */
        outb((inb(0x61) & ~0x02) | 0x01, 0x61);

        /*
         * Counter 2, mode 0 (one-shot), binary count
         *
         * NOTE! Mode 2 decrements by two (and then the
         * output is flipped each time, giving the same
         * final output frequency as a decrement-by-one),
         * so mode 0 is much better when looking at the
         * individual counts.
         */
        outb(0xb0, 0x43);

        /* Start at 0xffff */
        outb(0xff, 0x42);
        outb(0xff, 0x42);

        /*
         * The PIT starts counting at the next edge, so we
         * need to delay for a microsecond. The easiest way
         * to do that is to just read back the 16-bit counter
         * once from the PIT.
         */
        pit_verify_msb(0);

        if (pit_expect_msb(0xff, &tsc, &d1)) {
                for (i = 1; i <= MAX_QUICK_PIT_ITERATIONS; i++) {
                        if (!pit_expect_msb(0xff-i, &delta, &d2))
                                break;

                        delta -= tsc;

                        /*
                         * Extrapolate the error and fail fast if the error will
                         * never be below 500 ppm.
                         */
                        if (i == 1 &&
                            d1 + d2 >= (delta * MAX_QUICK_PIT_ITERATIONS) >> 11)
                                return 0;

                        /*
                         * Iterate until the error is less than 500 ppm
                         */
                        if (d1+d2 >= delta >> 11)
                                continue;

                        /*
                         * Check the PIT one more time to verify that
                         * all TSC reads were stable wrt the PIT.
                         *
                         * This also guarantees serialization of the
                         * last cycle read ('d2') in pit_expect_msb.
                         */
                        if (!pit_verify_msb(0xfe - i))
                                break;
                        goto success;
                }
        }
        pr_info("fast TSC calibration failed\n");
        return 0;

success:
        /*
         * Ok, if we get here, then we've seen the
         * MSB of the PIT decrement 'i' times, and the
         * error has shrunk to less than 500 ppm.
         *
         * As a result, we can depend on there not being
         * any odd delays anywhere, and the TSC reads are
         * reliable (within the error).
         *
         * kHz = ticks / time-in-seconds / 1000;
         * kHz = (t2 - t1) / (I * 256 / PIT_TICK_RATE) / 1000
         * kHz = ((t2 - t1) * PIT_TICK_RATE) / (I * 256 * 1000)
         */
        delta *= PIT_TICK_RATE;
        do_div(delta, i*256*1000);
        pr_info("fast TSC calibration using PIT\n");
        return delta;
}

void tsc_init(void)
{
        const char *verb = "";

        tsc_khz = native_calibrate_tsc();
        if (!tsc_khz)
                tsc_khz = quick_pit_calibrate();
        if (!tsc_khz) {
                verb = "assume ";
                tsc_khz = 2000000;
        }
        pr_info("%s%lu.%03lu MHz\n",
                verb, tsc_khz / 1000, tsc_khz % 1000);
}

useconds_t uptime(void)
{
        if (!tsc_khz)
                return 0;

        /*
         * convert cyles to microseconds:
         *   us = cycles / (freq / us_per_sec)
         *   us = cycles * (us_per_sec / freq)
         *   us = cycles * (10^6 / (cpu_khz * 10^3))
         *   us = cycles * (10^3 / cpu_khz)
         */
        return get_cycles() * 1000 / tsc_khz;
}

void udelay(useconds_t usecs)
{
        useconds_t t0 = uptime();

        if (!t0)
                return;

        while (uptime() - t0 < usecs)
                cpu_relax();
}
