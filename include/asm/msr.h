#pragma once

#include <asm/msr-index.h>
#include <io/const.h>

static inline void rdmsr(uint32_t msr, uint32_t *low, uint32_t *high)
{
        asm volatile("rdmsr" : "=a" (*low), "=d" (*high) : "c" (msr));
}

static inline void wrmsr(uint32_t msr, uint32_t low, uint32_t high)
{
        asm volatile("wrmsr" : : "c" (msr), "a" (low), "d" (high) : "memory");
}

static inline uint64_t rdmsrl(uint32_t msr)
{
        uint32_t low, high;

        rdmsr(msr, &low, &high);
        return low | ((uint64_t)high << 32);
}

static inline void wrmsrl(uint32_t msr, uint64_t val)
{
        wrmsr(msr, (uint32_t)val, (uint32_t)(val >> 32));
}
