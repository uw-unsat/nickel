#pragma once

#include <asm/desc.h>
#include <sys/types.h>

/*
 * Address types:
 *
 *  gva - guest virtual address
 *  gpa - guest physical address
 *  gfn - guest frame number
 *  hva - host virtual address
 *  hpa - host physical address
 *  hfn - host frame number
 */

typedef unsigned long  gva_t;
typedef uint64_t       gpa_t;
typedef uint64_t       gfn_t;

typedef unsigned long  hva_t;
typedef uint64_t       hpa_t;
typedef uint64_t       hfn_t;

struct kvm_segment {
        uint64_t base;
        uint32_t limit;
        uint16_t selector;
        uint8_t  type;
        uint8_t  present, dpl, db, s, l, g, avl;
        uint8_t  unusable;
        uint8_t  padding;
};
