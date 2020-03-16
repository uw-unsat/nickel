#pragma once

#include <stdio.h>
#include <stdint.h>
#include <nistar/assert.h>

#define __packed                __attribute__((packed))

static inline uint64_t rdtsc(void)
{
        uint64_t low, high;

        asm volatile("rdtsc" : "=a" (low), "=d" (high));

        return low | (high << 32);
}

static inline uint32_t sys_now(void)
{
        extern uint64_t sys_debug_uptime(void);

        return (uint32_t) sys_debug_uptime();
}


#define LWIP_PLATFORM_DIAG(x)                                                                      \
    do {                                                                                           \
        printf x;                                                                                 \
    } while (0)
#define LWIP_PLATFORM_ASSERT(x) panic(x)

#ifndef LITTLE_ENDIAN
#error LITTLE_ENDIAN not defined
#endif

#define PACK_STRUCT_STRUCT __packed

/* suppress compiler warning */
#define X8_F "02x"

#define LWIP_RAND rdtsc

