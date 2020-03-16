#pragma once

#include <asm/percpu.h>
#include <asm/threads.h>
#include <sys/types.h>

#define DECLARE_PER_CPU(type, name)     \
        extern typeof(type) name

#define DEFINE_PER_CPU(type, name)      \
        typeof(type) name __section(.percpu)

#define per_cpu_ptr(ptr, cpu)           \
        RELOC_HIDE(ptr, per_cpu_offset(cpu))

#define per_cpu(var, cpu)               \
        (*per_cpu_ptr(&(var), cpu))

#define this_cpu_ptr(ptr)               \
        per_cpu_ptr(ptr, smp_processor_id())

#define for_each_possible_cpu(cpu)      \
        for ((cpu) = 0; (cpu) < NR_CPUS; (cpu)++)

extern unsigned long __per_cpu_offset[NR_CPUS];

DECLARE_PER_CPU(int, cpu_number);

static inline __attribute_const__ int smp_processor_id(void)
{
#if NR_CPUS == 1
        return 0;
#else
        return this_cpu_read(cpu_number);
#endif
}

static inline unsigned long per_cpu_offset(int cpu)
{
#if NR_CPUS == 1
        return 0;
#else
        return __per_cpu_offset[cpu];
#endif
}
