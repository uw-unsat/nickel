#pragma once

#include <stdint.h>

struct mtrr_var_range {
        uint32_t base_lo;
        uint32_t base_hi;
        uint32_t mask_lo;
        uint32_t mask_hi;
};

/* In the Intel processor's MTRR interface, the MTRR type is always held in
   an 8 bit field: */
typedef uint8_t mtrr_type;

#define MTRR_NUM_FIXED_RANGES           88
#define MTRR_MAX_VAR_RANGES             256

struct mtrr_state_type {
        struct mtrr_var_range var_ranges[MTRR_MAX_VAR_RANGES];
        mtrr_type fixed_ranges[MTRR_NUM_FIXED_RANGES];
        unsigned char enabled;
        unsigned char have_fixed;
        mtrr_type def_type;
};

#define MTRRphysBase_MSR(reg) (0x200 + 2 * (reg))
#define MTRRphysMask_MSR(reg) (0x200 + 2 * (reg) + 1)

/* Bit fields for enabled in struct mtrr_state_type */
#define MTRR_STATE_MTRR_FIXED_ENABLED   0x01
#define MTRR_STATE_MTRR_ENABLED         0x02

/* MTRR memory types, which are defined in SDM */
#define MTRR_TYPE_UNCACHABLE 0
#define MTRR_TYPE_WRCOMB     1
/*#define MTRR_TYPE_         2*/
/*#define MTRR_TYPE_         3*/
#define MTRR_TYPE_WRTHROUGH  4
#define MTRR_TYPE_WRPROT     5
#define MTRR_TYPE_WRBACK     6
#define MTRR_NUM_TYPES       7

/*
 * Invalid MTRR memory type.  mtrr_type_lookup() returns this value when
 * MTRRs are disabled.  Note, this value is allocated from the reserved
 * values (0x7-0xff) of the MTRR memory types.
 */
#define MTRR_TYPE_INVALID    0xff

void mtrr_init(void);
const char *mtrr_attrib_to_str(int x);
uint8_t mtrr_type_lookup(uint64_t start, uint64_t end, uint8_t *uniform);
