#pragma once

#include <io/compiler.h>
#include <sys/bug.h>
#include <sys/printk.h>
#include <asm/tsc.h>

#define LWIP_PLATFORM_DIAG(x)                                                                      \
    do {                                                                                           \
        pr_info x;                                                                                 \
    } while (0)
#define LWIP_PLATFORM_ASSERT(x) panic(x)

#ifndef LITTLE_ENDIAN
#error LITTLE_ENDIAN not defined
#endif
// #define BYTE_ORDER LITTLE_ENDIAN

#define PACK_STRUCT_STRUCT __packed

/* suppress compiler warning */
#define X8_F "02x"

#define LWIP_RAND rdtsc

