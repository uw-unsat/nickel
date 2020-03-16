#define pr_fmt(fmt) __MODULE__ ": " fmt

#include <asm/cpufeature.h>
#include <asm/msr.h>
#include <asm/mtrr.h>

static struct mtrr_state_type mtrr_state;
static unsigned int num_var_ranges;

static unsigned last_fixed_start;
static unsigned last_fixed_end;
static mtrr_type last_fixed_type;

static uint64_t size_or_mask;

static unsigned int get_num_var_ranges(void)
{
        uint32_t config = 0, dummy;

        rdmsr(MSR_MTRRcap, &config, &dummy);
        return config & 0xff;
}

/* Get the MSR pair relating to a var range */
static void get_mtrr_var_range(unsigned int index, struct mtrr_var_range *vr)
{
        rdmsr(MTRRphysBase_MSR(index), &vr->base_lo, &vr->base_hi);
        rdmsr(MTRRphysMask_MSR(index), &vr->mask_lo, &vr->mask_hi);
}

static void get_fixed_ranges(mtrr_type *frs)
{
        unsigned int *p = (unsigned int *)frs;
        int i;

        rdmsr(MSR_MTRRfix64K_00000, &p[0], &p[1]);

        for (i = 0; i < 2; i++)
                rdmsr(MSR_MTRRfix16K_80000 + i, &p[2 + i * 2], &p[3 + i * 2]);
        for (i = 0; i < 8; i++)
                rdmsr(MSR_MTRRfix4K_C0000 + i, &p[6 + i * 2], &p[7 + i * 2]);
}

static const char *const mtrr_strings[] = {
        "uncachable",           /* 0 */
        "write-combining",      /* 1 */
        "?",                    /* 2 */
        "?",                    /* 3 */
        "write-through",        /* 4 */
        "write-protect",        /* 5 */
        "write-back",           /* 6 */
};

const char *mtrr_attrib_to_str(int x)
{
        return (x <= ARRAY_SIZE(mtrr_strings)) ? mtrr_strings[x] : "?";
}

static void print_fixed_last(void)
{
        if (!last_fixed_end)
                return;

        pr_info("  0x%05x-0x%05x %s\n",
                last_fixed_start, last_fixed_end - 1,
                mtrr_attrib_to_str(last_fixed_type));

        last_fixed_end = 0;
}

static void update_fixed_last(unsigned base, unsigned end, mtrr_type type)
{
        last_fixed_start = base;
        last_fixed_end = end;
        last_fixed_type = type;
}

static void print_fixed(unsigned base, unsigned step, const mtrr_type *types)
{
        unsigned i;

        for (i = 0; i < 8; ++i, ++types, base += step) {
                if (last_fixed_end == 0) {
                        update_fixed_last(base, base + step, *types);
                        continue;
                }
                if (last_fixed_end == base && last_fixed_type == *types) {
                        last_fixed_end = base + step;
                        continue;
                }
                /* new segments: gap or different type */
                print_fixed_last();
                update_fixed_last(base, base + step, *types);
        }
}

static void print_mtrr_state(void)
{
        unsigned int i;
        int high_width;

        pr_info("default type: %s\n",
                mtrr_attrib_to_str(mtrr_state.def_type));
        if (mtrr_state.have_fixed) {
                pr_info("fixed ranges %sabled\n",
                        ((mtrr_state.enabled & MTRR_STATE_MTRR_ENABLED) &&
                         (mtrr_state.enabled & MTRR_STATE_MTRR_FIXED_ENABLED)) ?
                         "en" : "dis");
                print_fixed(0x00000, 0x10000, mtrr_state.fixed_ranges + 0);
                for (i = 0; i < 2; ++i)
                        print_fixed(0x80000 + i * 0x20000, 0x04000,
                                    mtrr_state.fixed_ranges + (i + 1) * 8);
                for (i = 0; i < 8; ++i)
                        print_fixed(0xC0000 + i * 0x08000, 0x01000,
                                    mtrr_state.fixed_ranges + (i + 3) * 8);

                /* tail */
                print_fixed_last();
        }
        pr_info("variable ranges %sabled\n",
                mtrr_state.enabled & MTRR_STATE_MTRR_ENABLED ? "en" : "dis");
        high_width = (__ffs(size_or_mask) - (32 - PAGE_SHIFT) + 3) / 4;

        for (i = 0; i < num_var_ranges; ++i) {
                if (mtrr_state.var_ranges[i].mask_lo & (1 << 11))
                        pr_info("  %u base 0x%0*x%05x000 mask 0x%0*x%05x000 %s\n",
                                i,
                                high_width,
                                mtrr_state.var_ranges[i].base_hi,
                                mtrr_state.var_ranges[i].base_lo >> 12,
                                high_width,
                                mtrr_state.var_ranges[i].mask_hi,
                                mtrr_state.var_ranges[i].mask_lo >> 12,
                                mtrr_attrib_to_str(mtrr_state.var_ranges[i].base_lo & 0xff));
                else
                        pr_info("  %u disabled\n", i);
        }
}

static bool get_mtrr_state(void)
{
        struct mtrr_var_range *vrs;
        uint32_t lo, dummy;
        unsigned int i;

        vrs = mtrr_state.var_ranges;

        rdmsr(MSR_MTRRcap, &lo, &dummy);
        mtrr_state.have_fixed = (lo >> 8) & 1;

        for (i = 0; i < num_var_ranges; i++)
                get_mtrr_var_range(i, &vrs[i]);
        if (mtrr_state.have_fixed)
                get_fixed_ranges(mtrr_state.fixed_ranges);

        rdmsr(MSR_MTRRdefType, &lo, &dummy);
        mtrr_state.def_type = (lo & 0xff);
        mtrr_state.enabled = (lo & 0xc00) >> 10;

        print_mtrr_state();

        return !!(mtrr_state.enabled & MTRR_STATE_MTRR_ENABLED);
}

#define SIZE_OR_MASK_BITS(n)  (~((1ULL << ((n) - PAGE_SHIFT)) - 1))

void mtrr_init(void)
{
        BUG_ON(!this_cpu_has(X86_FEATURE_MTRR));

        size_or_mask = SIZE_OR_MASK_BITS(36);

        num_var_ranges = get_num_var_ranges();
        get_mtrr_state();
}

/* Get the size of contiguous MTRR range */
static uint64_t get_mtrr_size(uint64_t mask)
{
        uint64_t size;

        mask >>= PAGE_SHIFT;
        mask |= size_or_mask;
        size = -mask;
        size <<= PAGE_SHIFT;
        return size;
}

/*
 * Check and return the effective type for MTRR-MTRR type overlap.
 * Returns 1 if the effective type is UNCACHEABLE, else returns 0
 */
static int check_type_overlap(uint8_t *prev, uint8_t *curr)
{
        if (*prev == MTRR_TYPE_UNCACHABLE || *curr == MTRR_TYPE_UNCACHABLE) {
                *prev = MTRR_TYPE_UNCACHABLE;
                *curr = MTRR_TYPE_UNCACHABLE;
                return 1;
        }

        if ((*prev == MTRR_TYPE_WRBACK && *curr == MTRR_TYPE_WRTHROUGH) ||
            (*prev == MTRR_TYPE_WRTHROUGH && *curr == MTRR_TYPE_WRBACK)) {
                *prev = MTRR_TYPE_WRTHROUGH;
                *curr = MTRR_TYPE_WRTHROUGH;
        }

        if (*prev != *curr) {
                *prev = MTRR_TYPE_UNCACHABLE;
                *curr = MTRR_TYPE_UNCACHABLE;
                return 1;
        }

        return 0;
}

/**
 * mtrr_type_lookup_fixed - look up memory type in MTRR fixed entries
 *
 * Return the MTRR fixed memory type of 'start'.
 *
 * MTRR fixed entries are divided into the following ways:
 *  0x00000 - 0x7FFFF : This range is divided into eight 64KB sub-ranges
 *  0x80000 - 0xBFFFF : This range is divided into sixteen 16KB sub-ranges
 *  0xC0000 - 0xFFFFF : This range is divided into sixty-four 4KB sub-ranges
 *
 * Return Values:
 * MTRR_TYPE_(type)  - Matched memory type
 * MTRR_TYPE_INVALID - Unmatched
 */
static uint8_t mtrr_type_lookup_fixed(uint64_t start, uint64_t end)
{
        int idx;

        if (start >= 0x100000)
                return MTRR_TYPE_INVALID;

        /* 0x0 - 0x7FFFF */
        if (start < 0x80000) {
                idx = 0;
                idx += (start >> 16);
                return mtrr_state.fixed_ranges[idx];
        /* 0x80000 - 0xBFFFF */
        } else if (start < 0xC0000) {
                idx = 1 * 8;
                idx += ((start - 0x80000) >> 14);
                return mtrr_state.fixed_ranges[idx];
        }

        /* 0xC0000 - 0xFFFFF */
        idx = 3 * 8;
        idx += ((start - 0xC0000) >> 12);
        return mtrr_state.fixed_ranges[idx];
}

/**
 * mtrr_type_lookup_variable - look up memory type in MTRR variable entries
 *
 * Return Value:
 * MTRR_TYPE_(type) - Matched memory type or default memory type (unmatched)
 *
 * Output Arguments:
 * repeat - Set to 1 when [start:end] spanned across MTRR range and type
 *          returned corresponds only to [start:*partial_end].  Caller has
 *          to lookup again for [*partial_end:end].
 *
 * uniform - Set to 1 when an MTRR covers the region uniformly, i.e. the
 *           region is fully covered by a single MTRR entry or the default
 *           type.
 */
static uint8_t mtrr_type_lookup_variable(uint64_t start, uint64_t end,
                                         uint64_t *partial_end,
                                         int *repeat, uint8_t *uniform)
{
        int i;
        uint64_t base, mask;
        uint8_t prev_match, curr_match;

        *repeat = 0;
        *uniform = 1;

        /* Make end inclusive instead of exclusive */
        end--;

        prev_match = MTRR_TYPE_INVALID;
        for (i = 0; i < num_var_ranges; ++i) {
                unsigned short start_state, end_state, inclusive;

                if (!(mtrr_state.var_ranges[i].mask_lo & (1 << 11)))
                        continue;

                base = (((uint64_t)mtrr_state.var_ranges[i].base_hi) << 32) +
                       (mtrr_state.var_ranges[i].base_lo & PAGE_MASK);
                mask = (((uint64_t)mtrr_state.var_ranges[i].mask_hi) << 32) +
                       (mtrr_state.var_ranges[i].mask_lo & PAGE_MASK);

                start_state = ((start & mask) == (base & mask));
                end_state = ((end & mask) == (base & mask));
                inclusive = ((start < base) && (end > base));

                if ((start_state != end_state) || inclusive) {
                        /*
                         * We have start:end spanning across an MTRR.
                         * We split the region into either
                         *
                         * - start_state:1
                         * (start:mtrr_end)(mtrr_end:end)
                         * - end_state:1
                         * (start:mtrr_start)(mtrr_start:end)
                         * - inclusive:1
                         * (start:mtrr_start)(mtrr_start:mtrr_end)(mtrr_end:end)
                         *
                         * depending on kind of overlap.
                         *
                         * Return the type of the first region and a pointer
                         * to the start of next region so that caller will be
                         * advised to lookup again after having adjusted start
                         * and end.
                         *
                         * Note: This way we handle overlaps with multiple
                         * entries and the default type properly.
                         */
                        if (start_state)
                                *partial_end = base + get_mtrr_size(mask);
                        else
                                *partial_end = base;

                        if (*partial_end <= start)
                                *partial_end = start + PAGE_SIZE;

                        end = *partial_end - 1; /* end is inclusive */
                        *repeat = 1;
                        *uniform = 0;
                }

                if ((start & mask) != (base & mask))
                        continue;

                curr_match = mtrr_state.var_ranges[i].base_lo & 0xff;
                if (prev_match == MTRR_TYPE_INVALID) {
                        prev_match = curr_match;
                        continue;
                }

                *uniform = 0;
                if (check_type_overlap(&prev_match, &curr_match))
                        return curr_match;
        }

        if (prev_match != MTRR_TYPE_INVALID)
                return prev_match;

        return mtrr_state.def_type;
}

/**
 * mtrr_type_lookup - look up memory type in MTRR
 *
 * Return Values:
 * MTRR_TYPE_(type)  - The effective MTRR type for the region
 * MTRR_TYPE_INVALID - MTRR is disabled
 *
 * Output Argument:
 * uniform - Set to 1 when an MTRR covers the region uniformly, i.e. the
 *           region is fully covered by a single MTRR entry or the default
 *           type.
 */
uint8_t mtrr_type_lookup(uint64_t start, uint64_t end, uint8_t *uniform)
{
        uint8_t type, prev_type, is_uniform = 1, dummy;
        int repeat;
        uint64_t partial_end;

        if (!(mtrr_state.enabled & MTRR_STATE_MTRR_ENABLED))
                return MTRR_TYPE_INVALID;

        /*
         * Look up the fixed ranges first, which take priority over
         * the variable ranges.
         */
        if ((start < 0x100000) &&
            (mtrr_state.have_fixed) &&
            (mtrr_state.enabled & MTRR_STATE_MTRR_FIXED_ENABLED)) {
                is_uniform = 0;
                type = mtrr_type_lookup_fixed(start, end);
                goto out;
        }

        /*
         * Look up the variable ranges.  Look of multiple ranges matching
         * this address and pick type as per MTRR precedence.
         */
        type = mtrr_type_lookup_variable(start, end, &partial_end,
                                         &repeat, &is_uniform);

        /*
         * Common path is with repeat = 0.
         * However, we can have cases where [start:end] spans across some
         * MTRR ranges and/or the default type.  Do repeated lookups for
         * that case here.
         */
        while (repeat) {
                prev_type = type;
                start = partial_end;
                is_uniform = 0;
                type = mtrr_type_lookup_variable(start, end, &partial_end,
                                                 &repeat, &dummy);

                if (check_type_overlap(&prev_type, &type))
                        goto out;
        }

out:
        *uniform = is_uniform;
        return type;
}
