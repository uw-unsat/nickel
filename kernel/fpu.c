#define pr_fmt(fmt) __MODULE__ ": " fmt

#include <asm/cpufeature.h>
#include <asm/fpu.h>

/*
 * We use either xsaveopt/xrstor (standard) or xsaves/xrstors (compacted).
 * QEMU TCG doesn't support xsaves/xrstors yet; KVM and Bochs do.
 */

static uint64_t xfeatures_mask;
size_t fpu_kernel_xstate_size;
union fpregs_state init_fpstate;

static const char *xfeature_names[] =
{
        "x87 floating point registers"  ,
        "SSE registers"                 ,
        "AVX registers"                 ,
        "MPX bounds registers"          ,
        "MPX CSR"                       ,
        "AVX-512 opmask"                ,
        "AVX-512 Hi256"                 ,
        "AVX-512 ZMM_Hi256"             ,
        "Processor Trace (unused)"      ,
        "Protection Keys User registers",
        "unknown xstate feature"        ,
};

static short xsave_cpuid_features[] = {
        X86_FEATURE_FPU,
        X86_FEATURE_XMM,
        X86_FEATURE_AVX,
        X86_FEATURE_MPX,
        X86_FEATURE_MPX,
        X86_FEATURE_AVX512F,
        X86_FEATURE_AVX512F,
        X86_FEATURE_AVX512F,
        X86_FEATURE_INTEL_PT,
        X86_FEATURE_PKU,
};

static void xfeatures_init(void)
{
        uint32_t eax, ebx, ecx, edx;
        size_t i;

        cpuid_count(XSTATE_CPUID, 0, &eax, &ebx, &ecx, &edx);
        xfeatures_mask = eax + ((uint64_t)edx << 32);
        /* FP/SSE must exist */
        BUG_ON((xfeatures_mask & XFEATURE_MASK_FPSSE) != XFEATURE_MASK_FPSSE);

        for (i = 0; i < ARRAY_SIZE(xsave_cpuid_features); i++) {
                if (!this_cpu_has(xsave_cpuid_features[i]))
                        xfeatures_mask &= ~BIT_64(i);
        }

        /* currently supported features */
        xfeatures_mask &= XCNTXT_MASK;
        /* no supervisor state support yet */
        BUG_ON(xfeatures_mask & XFEATURE_MASK_SUPERVISOR);

        for (i = 0; i < XFEATURE_MAX; ++i) {
                unsigned long xstate_mask = 1UL << i;

                if (!(xfeatures_mask & xstate_mask))
                        continue;
                pr_info("XSAVE-supported feature 0x%03lx: %s\n", xstate_mask, xfeature_names[i]);
        }
}

/*
 * Get total size of enabled xstates in XCR0/xfeatures_mask.
 *
 * Note the SDM's wording here.  "sub-function 0" only enumerates
 * the size of the *user* states.  If we use it to size a buffer
 * that we use 'XSAVES' on, we could potentially overflow the
 * buffer because 'XSAVES' saves system states too.
 *
 * Note that we do not currently set any bits on IA32_XSS so
 * 'XCR0 | IA32_XSS == XCR0' for now.
 */
static unsigned int get_xsaves_size(void)
{
        unsigned int eax, ebx, ecx, edx;
        /*
         * - CPUID function 0DH, sub-function 1:
         *    EBX enumerates the size (in bytes) required by
         *    the XSAVES instruction for an XSAVE area
         *    containing all the state components
         *    corresponding to bits currently set in
         *    XCR0 | IA32_XSS.
         */
        cpuid_count(XSTATE_CPUID, 1, &eax, &ebx, &ecx, &edx);
        return ebx;
}

static unsigned int get_xsave_size(void)
{
        unsigned int eax, ebx, ecx, edx;
        /*
         * - CPUID function 0DH, sub-function 0:
         *    EBX enumerates the size (in bytes) required by
         *    the XSAVE instruction for an XSAVE area
         *    containing all the *user* state components
         *    corresponding to bits currently set in XCR0.
         */
        cpuid_count(XSTATE_CPUID, 0, &eax, &ebx, &ecx, &edx);
        return ebx;
}

static void xstate_setup(void)
{
        bool has_xsaves;

        has_xsaves = this_cpu_has(X86_FEATURE_XSAVES);
        fpu_kernel_xstate_size = has_xsaves ? get_xsaves_size() : get_xsave_size();
        BUG_ON(sizeof(union fpregs_state) < fpu_kernel_xstate_size);

        pr_info("XSAVE-managed state %zu bytes ('%s' format)\n",
                fpu_kernel_xstate_size, has_xsaves ? "compacted" : "standard");

        /*
         * Init all the features state with header.xfeatures being 0x0,
         * and dump the init state again. This is to identify the init state
         * of any feature which is not represented by all zero's.
         */
        if (has_xsaves)
                init_fpstate.xsave.header.xcomp_bv = XCOMP_BV_COMPACTED_FORMAT | xfeatures_mask;
        copy_kernel_to_xregs(&init_fpstate.xsave);
        copy_xregs_to_kernel(&init_fpstate.xsave);
}

static void xstate_init(void)
{
        bool is_system_init = !xfeatures_mask;

        if (is_system_init)
                xfeatures_init();

        xsetbv(XCR_XFEATURE_ENABLED_MASK, xfeatures_mask);

        if (is_system_init)
                xstate_setup();
}

void fpu_init(void)
{
        unsigned long cr0;

        BUG_ON(!this_cpu_has(X86_FEATURE_FXSR));
        BUG_ON(!this_cpu_has(X86_FEATURE_XMM));
        cr4_set_bits(X86_CR4_OSFXSR | X86_CR4_OSXMMEXCPT);

        cr0 = read_cr0();
        cr0 &= ~(X86_CR0_TS|X86_CR0_EM); /* clear TS and EM */
        BUG_ON(!this_cpu_has(X86_FEATURE_FPU));
        write_cr0(cr0);

        /* flush out any pending x87 state */
        asm volatile("fninit");

        BUG_ON(!this_cpu_has(X86_FEATURE_XSAVE));
        BUG_ON(!this_cpu_has(X86_FEATURE_XSAVEOPT));
        cr4_set_bits(X86_CR4_OSXSAVE);

        xstate_init();
}

void copy_xregs_to_kernel(void *xstate)
{
        uint64_t mask = ~UINT64_C(0);

        if (this_cpu_has(X86_FEATURE_XSAVES))
                xsaves(xstate, mask);
        else
                xsaveopt(xstate, mask);
}

void copy_kernel_to_xregs(void *xstate)
{
        uint64_t mask = ~UINT64_C(0);

        if (this_cpu_has(X86_FEATURE_XSAVES))
                xrstors(xstate, mask);
        else
                xrstor(xstate, mask);
}
