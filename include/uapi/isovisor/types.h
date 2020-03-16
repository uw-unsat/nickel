#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#define PM_READ         (1 << 0)
#define PM_WRITE        (1 << 1)
#define PM_EXECUTE      (1 << 2)

/* enclave page number */
typedef uint64_t        epn_t;
/* shared page number */
typedef uint64_t        spn_t;

typedef uint64_t        bool64_t;

enum page_type {
        PT_FREE,
        PT_SECS,
        PT_TCS,
        PT_REG,
        PT_FORCE_WIDTH = UINT64_C(0xffffffffffffffff),
};

_Static_assert(sizeof(enum page_type) == 8, "page_type must be 64-bit");

struct page_desc {
        uint64_t type;
        epn_t secs;
        uint64_t address;
        uint64_t perm;
};

struct secs {
        uint64_t size;
        uint64_t baseaddr;
        uint64_t xfrm;
        bool64_t sealed;
        bool64_t stopped;
        size_t   nr_pages;
};

/* thread control structure: match SGX */

struct tcs {
        uint64_t stage;
        uint64_t flags;
        uint64_t ossa;
        uint64_t cssa;
        uint64_t nssa;
        uint64_t oentry;
        uint64_t aep;
        uint64_t ofsbasgx;
        uint64_t ogsbasgx;
};

/* SSA data structures: match SGX as they are visible inside enclaves */

struct exinfo {
        uint64_t maddr;
        uint32_t errcd;
        uint32_t reserved;
};

struct gprsgx {
        uint64_t rax;
        uint64_t rcx;
        uint64_t rdx;
        uint64_t rbx;
        uint64_t rsp;
        uint64_t rbp;
        uint64_t rsi;
        uint64_t rdi;
        uint64_t r8;
        uint64_t r9;
        uint64_t r10;
        uint64_t r11;
        uint64_t r12;
        uint64_t r13;
        uint64_t r14;
        uint64_t r15;
        uint64_t rflags;
        uint64_t rip;
        uint64_t ursp;
        uint64_t urbp;
        uint32_t exitinfo;
        uint32_t reserved;
        uint64_t fsbase;
        uint64_t gsbase;
};

struct ssaframe {
        /* XSAVE region & padding */
        uint8_t xsave[4096 - sizeof(struct exinfo) - sizeof(struct gprsgx)];
        /* MISC region */
        struct exinfo exinfo;
        /* GPRSGX region */
        struct gprsgx gprsgx;
};
