#pragma once

#include <sys/bug.h>

/*
 * Bitfield access macros
 *
 * FIELD_{GET,PREP} macros take as first parameter shifted mask
 * from which they extract the base mask and shift amount.
 * Mask must be a compilation time constant.
 *
 * Example:
 *
 *  #define REG_FIELD_A  GENMASK(6, 0)
 *  #define REG_FIELD_B  BIT(7)
 *  #define REG_FIELD_C  GENMASK(15, 8)
 *  #define REG_FIELD_D  GENMASK(31, 16)
 *
 * Get:
 *  a = FIELD_GET(REG_FIELD_A, reg);
 *  b = FIELD_GET(REG_FIELD_B, reg);
 *
 * Set:
 *  reg = FIELD_PREP(REG_FIELD_A, 1) |
 *        FIELD_PREP(REG_FIELD_B, 0) |
 *        FIELD_PREP(REG_FIELD_C, c) |
 *        FIELD_PREP(REG_FIELD_D, 0x40);
 *
 * Modify:
 *  reg &= ~REG_FIELD_C;
 *  reg |= FIELD_PREP(REG_FIELD_C, c);
 */

#define __bf_shf(x) (__builtin_ffsll(x) - 1)

#define __BF_FIELD_CHECK(_mask, _reg, _val, _pfx)                       \
        ({                                                              \
                BUILD_BUG_ON_MSG(!__builtin_constant_p(_mask),          \
                                 _pfx "mask is not constant");          \
                BUILD_BUG_ON_MSG(!(_mask), _pfx "mask is zero");        \
                BUILD_BUG_ON_MSG(__builtin_constant_p(_val) ?           \
                                 ~((_mask) >> __bf_shf(_mask)) & (_val) : 0, \
                                 _pfx "value too large for the field"); \
                BUILD_BUG_ON_MSG((_mask) > (typeof(_reg))~0ull,         \
                                 _pfx "type of reg too small for mask"); \
                BUILD_BUG_ON_NOT_POWER_OF_2((_mask) +                   \
                                            (1ULL << __bf_shf(_mask))); \
        })

/**
 * FIELD_FIT() - check if value fits in the field
 * @_mask: shifted mask defining the field's length and position
 * @_val:  value to test against the field
 *
 * Return: true if @_val can fit inside @_mask, false if @_val is too big.
 */
#define FIELD_FIT(_mask, _val)                                          \
        ({                                                              \
                __BF_FIELD_CHECK(_mask, 0ULL, _val, "FIELD_FIT: ");     \
                !((((typeof(_mask))_val) << __bf_shf(_mask)) & ~(_mask)); \
        })

/**
 * FIELD_PREP() - prepare a bitfield element
 * @_mask: shifted mask defining the field's length and position
 * @_val:  value to put in the field
 *
 * FIELD_PREP() masks and shifts up the value.  The result should
 * be combined with other fields of the bitfield using logical OR.
 */
#define FIELD_PREP(_mask, _val)                                         \
        ({                                                              \
                __BF_FIELD_CHECK(_mask, 0ULL, _val, "FIELD_PREP: ");    \
                ((typeof(_mask))(_val) << __bf_shf(_mask)) & (_mask);   \
        })

/**
 * FIELD_GET() - extract a bitfield element
 * @_mask: shifted mask defining the field's length and position
 * @_reg:  value of entire bitfield
 *
 * FIELD_GET() extracts the field specified by @_mask from the
 * bitfield passed in as @_reg by masking and shifting it down.
 */
#define FIELD_GET(_mask, _reg)                                          \
        ({                                                              \
                __BF_FIELD_CHECK(_mask, _reg, 0U, "FIELD_GET: ");       \
                (typeof(_mask))(((_reg) & (_mask)) >> __bf_shf(_mask)); \
        })
