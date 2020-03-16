#pragma once

#include <asm/cpufeatures.h>
#include <asm/intel-family.h>
#include <asm/processor-flags.h>
#include <sys/percpu.h>
#include <sys/types.h>

#define X86_VENDOR_INTEL        0
#define X86_VENDOR_CYRIX        1
#define X86_VENDOR_AMD          2
#define X86_VENDOR_UMC          3
#define X86_VENDOR_CENTAUR      5
#define X86_VENDOR_TRANSMETA    7
#define X86_VENDOR_NSC          8
#define X86_VENDOR_NUM          9

#define X86_VENDOR_UNKNOWN      0xff

struct cpuinfo_x86 {
        uint8_t                 x86;            /* CPU family */
        uint8_t                 x86_vendor;
        uint8_t                 x86_model;
        uint8_t                 x86_mask;
        /* Max extended CPUID function supported: */
        uint32_t                extended_cpuid_level;
        /* Maximum supported CPUID level, -1=no CPUID: */
        int                     cpuid_level;
        uint32_t                x86_capability[NCAPINTS + NBUGINTS];
        char                    x86_vendor_id[16];
        char                    x86_model_id[64];
        /* Index into per_cpu list: */
        uint16_t                cpu_index;
        uint32_t                microcode;
};

DECLARE_PER_CPU(struct cpuinfo_x86, cpu_info);
#define cpu_data(cpu)           per_cpu(cpu_info, cpu)
#define boot_cpu_data           cpu_data(0)

/*
 * This is the TSS defined by the hardware;
 * must not cross a page boundary.
 */
struct tss {
        uint32_t                reserved1;
        uint64_t                sp0;
        uint64_t                sp1;
        uint64_t                sp2;
        uint64_t                reserved2;
        uint64_t                ist[7];
        uint32_t                reserved3;
        uint32_t                reserved4;
        uint16_t                reserved5;
        uint16_t                io_bitmap_base;
} __packed;

/* we don't use IO permission bitmap */
#define INVALID_IO_BITMAP_OFFSET        0x8000
#define KERNEL_TSS_LIMIT                (sizeof(struct tss) - 1)

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

/*
 * Generic CPUID function
 * clear %ecx since some cpus (Cyrix MII) do not set or clear %ecx
 * resulting in stale register contents being returned.
 */
static inline void cpuid(unsigned int op,
                         unsigned int *eax, unsigned int *ebx,
                         unsigned int *ecx, unsigned int *edx)
{
        *eax = op;
        *ecx = 0;
        native_cpuid(eax, ebx, ecx, edx);
}

/* Some CPUID calls want 'count' to be placed in ecx */
static inline void cpuid_count(unsigned int op, int count,
                               unsigned int *eax, unsigned int *ebx,
                               unsigned int *ecx, unsigned int *edx)
{
        *eax = op;
        *ecx = count;
        native_cpuid(eax, ebx, ecx, edx);
}

/*
 * CPUID functions returning a single datum
 */
static inline unsigned int cpuid_eax(unsigned int op)
{
        unsigned int eax, ebx, ecx, edx;

        cpuid(op, &eax, &ebx, &ecx, &edx);

        return eax;
}

static inline unsigned int cpuid_ebx(unsigned int op)
{
        unsigned int eax, ebx, ecx, edx;

        cpuid(op, &eax, &ebx, &ecx, &edx);

        return ebx;
}

static inline unsigned int cpuid_ecx(unsigned int op)
{
        unsigned int eax, ebx, ecx, edx;

        cpuid(op, &eax, &ebx, &ecx, &edx);

        return ecx;
}

static inline unsigned int cpuid_edx(unsigned int op)
{
        unsigned int eax, ebx, ecx, edx;

        cpuid(op, &eax, &ebx, &ecx, &edx);

        return edx;
}

/* REP NOP (PAUSE) is a good thing to insert into busy-wait loops. */
static __always_inline void cpu_relax(void)
{
        asm volatile("rep; nop" ::: "memory");
}

static inline unsigned long save_flags(void)
{
        unsigned long flags;

        /*
         * "=rm" is safe here, because "pop" adjusts the stack before
         * it evaluates its effective address -- this is part of the
         * documented behavior of the "pop" instruction.
         */
        asm volatile("pushf ; pop %0"
                     : "=rm" (flags)
                     : /* no input */
                     : "memory");

        return flags;
}

static inline void restore_flags(unsigned long flags)
{
        asm volatile("push %0 ; popf"
                     : /* no output */
                     : "g" (flags)
                     : "memory", "cc");
}

static inline void cli(void)
{
        asm volatile("cli" : : : "memory");
}

static inline void sti(void)
{
        asm volatile("sti" : : : "memory");
}

static inline void halt(void)
{
        asm volatile("hlt" : : : "memory");
}

static inline unsigned long read_cr0(void)
{
        unsigned long val;

        asm volatile("mov %%cr0,%0\n\t" : "=r" (val) : : "memory");
        return val;
}

static inline void write_cr0(unsigned long val)
{
        asm volatile("mov %0,%%cr0": : "r" (val) : "memory");
}

static inline unsigned long read_cr2(void)
{
        unsigned long val;

        asm volatile("mov %%cr2,%0\n\t" : "=r" (val) : : "memory");
        return val;
}

static inline void write_cr2(unsigned long val)
{
        asm volatile("mov %0,%%cr2": : "r" (val) : "memory");
}

static inline unsigned long read_cr3(void)
{
        unsigned long val;

        asm volatile("mov %%cr3,%0" : "=r" (val) : : "memory");
        return val;
}

static inline void write_cr3(unsigned long val)
{
        asm volatile("mov %0,%%cr3": : "r" (val) : "memory");
}

static inline unsigned long read_cr4(void)
{
        unsigned long val;

        asm volatile("mov %%cr4,%0" : "=r" (val) : : "memory");
        return val;
}

static inline void write_cr4(unsigned long val)
{
        asm volatile("mov %0,%%cr4" : : "r" (val) : "memory");
}

static inline void cr4_set_bits(unsigned long mask)
{
        unsigned long cr4;

        cr4 = read_cr4();
        if ((cr4 | mask) != cr4)
                write_cr4(cr4 | mask);
}

static inline void prefetch(const void *x)
{
        asm volatile("prefetchnta %P1" : : "i" (0), "m" (*(const char *)x));
}
