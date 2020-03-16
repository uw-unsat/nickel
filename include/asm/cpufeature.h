#pragma once

#include <asm/processor.h>
#include <sys/bitops.h>

#define cpu_has(c, bit) \
         test_bit(bit, (unsigned long *)((c)->x86_capability))

#define cpu_has_bug(c, bit)     cpu_has(c, (bit))

#define this_cpu_has(bit)       cpu_has(this_cpu_ptr(&cpu_info), bit)

enum cpuid_leafs {
        CPUID_1_EDX             = 0,
        CPUID_8000_0001_EDX,
        CPUID_8086_0001_EDX,
        CPUID_LNX_1,
        CPUID_1_ECX,
        CPUID_C000_0001_EDX,
        CPUID_8000_0001_ECX,
        CPUID_LNX_2,
        CPUID_LNX_3,
        CPUID_7_0_EBX,
        CPUID_D_1_EAX,
        CPUID_F_0_EDX,
        CPUID_F_1_EDX,
        CPUID_8000_0008_EBX,
        CPUID_6_EAX,
        CPUID_8000_000A_EDX,
        CPUID_7_ECX,
        CPUID_8000_0007_EBX,
};

extern const char * const x86_cap_flags[NCAPINTS*32];
extern const char * const x86_bug_flags[NBUGINTS*32];
