#pragma once

#include <asm/cpufeature.h>

#define XSTATE_CPUID                    0x0000000d

/*
 * The legacy fx SSE/MMX FPU state format, as saved by FXSAVE and
 * restored by the FXRSTOR instructions. It's similar to the FSAVE
 * format, but differs in some areas, plus has extensions at
 * the end for the XMM registers.
 */
struct fxregs_state {
        uint16_t                        cwd; /* Control Word                    */
        uint16_t                        swd; /* Status Word                     */
        uint16_t                        twd; /* Tag Word                        */
        uint16_t                        fop; /* Last Instruction Opcode         */
        union {
                struct {
                        uint64_t        rip; /* Instruction Pointer             */
                        uint64_t        rdp; /* Data Pointer                    */
                };
                struct {
                        uint32_t        fip; /* FPU IP Offset                   */
                        uint32_t        fcs; /* FPU IP Selector                 */
                        uint32_t        foo; /* FPU Operand Offset              */
                        uint32_t        fos; /* FPU Operand Selector            */
                };
        };
        uint32_t                        mxcsr;          /* MXCSR Register State */
        uint32_t                        mxcsr_mask;     /* MXCSR Mask           */

        /* 8*16 bytes for each FP-reg = 128 bytes:                              */
        uint32_t                        st_space[32];

        /* 16*16 bytes for each XMM-reg = 256 bytes:                            */
        uint32_t                        xmm_space[64];

        uint32_t                        padding[12];

        union {
                uint32_t                padding1[12];
                uint32_t                sw_reserved[12];
        };
} __aligned(16);

/* Default value for fxregs_state.mxcsr: */
#define MXCSR_DEFAULT                   0x1f80

enum xfeature {
        XFEATURE_FP = 0,
        XFEATURE_SSE,
        /*
         * Values above here are "legacy states".
         * Those below are "extended states".
         */
        XFEATURE_YMM,
        XFEATURE_BNDREGS,
        XFEATURE_BNDCSR,
        XFEATURE_OPMASK,
        XFEATURE_ZMM_Hi256,
        XFEATURE_Hi16_ZMM,
        XFEATURE_PT_UNIMPLEMENTED_SO_FAR,
        XFEATURE_PKRU,

        XFEATURE_MAX,
};

#define XFEATURE_MASK_FP                (1 << XFEATURE_FP)
#define XFEATURE_MASK_SSE               (1 << XFEATURE_SSE)
#define XFEATURE_MASK_YMM               (1 << XFEATURE_YMM)
#define XFEATURE_MASK_BNDREGS           (1 << XFEATURE_BNDREGS)
#define XFEATURE_MASK_BNDCSR            (1 << XFEATURE_BNDCSR)
#define XFEATURE_MASK_OPMASK            (1 << XFEATURE_OPMASK)
#define XFEATURE_MASK_ZMM_Hi256         (1 << XFEATURE_ZMM_Hi256)
#define XFEATURE_MASK_Hi16_ZMM          (1 << XFEATURE_Hi16_ZMM)
#define XFEATURE_MASK_PT                (1 << XFEATURE_PT_UNIMPLEMENTED_SO_FAR)
#define XFEATURE_MASK_PKRU              (1 << XFEATURE_PKRU)

#define XFEATURE_MASK_FPSSE             (XFEATURE_MASK_FP | XFEATURE_MASK_SSE)
#define XFEATURE_MASK_AVX512            (XFEATURE_MASK_OPMASK \
                                         | XFEATURE_MASK_ZMM_Hi256 \
                                         | XFEATURE_MASK_Hi16_ZMM)

/* Supervisor features */
#define XFEATURE_MASK_SUPERVISOR        (XFEATURE_MASK_PT)

/* All currently supported features */
#define XCNTXT_MASK                     (XFEATURE_MASK_FP | \
                                         XFEATURE_MASK_SSE | \
                                         XFEATURE_MASK_YMM | \
                                         XFEATURE_MASK_OPMASK | \
                                         XFEATURE_MASK_ZMM_Hi256 | \
                                         XFEATURE_MASK_Hi16_ZMM  | \
                                         XFEATURE_MASK_PKRU | \
                                         XFEATURE_MASK_BNDREGS | \
                                         XFEATURE_MASK_BNDCSR)

struct xstate_header {
        uint64_t                        xfeatures;
        uint64_t                        xcomp_bv;
        uint64_t                        reserved[6];
} __packed;

/*
 * xstate_header.xcomp_bv[63] indicates that the extended_state_area
 * is in compacted format.
 */
#define XCOMP_BV_COMPACTED_FORMAT       BIT_64(63)

/*
 * This is our most modern FPU state format, as saved by the XSAVE
 * and restored by the XRSTOR instructions.
 *
 * It consists of a legacy fxregs portion, an xstate header and
 * subsequent areas as defined by the xstate header.  Not all CPUs
 * support all the extensions, so the size of the extended area
 * can vary quite a bit between CPUs.
 */
struct xregs_state {
        struct fxregs_state             i387;
        struct xstate_header            header;
        uint8_t                         extended_state_area[0];
} __packed __aligned(64);

/*
 * This union is used only for init_fpstate.
 */
union fpregs_state {
        struct xregs_state              xsave;
        uint8_t __padding[SZ_4K];
};

#define XCR_XFEATURE_ENABLED_MASK       0x00000000

static inline uint64_t xgetbv(uint32_t index)
{
        uint32_t eax, edx;

        asm volatile("xgetbv"
                     : "=a" (eax), "=d" (edx)
                     : "c" (index));
        return eax + ((uint64_t)edx << 32);
}

static inline void xsetbv(uint32_t index, uint64_t value)
{
        uint32_t eax = value;
        uint32_t edx = value >> 32;

        asm volatile("xsetbv"
                     : : "a" (eax), "d" (edx), "c" (index));
}

/* These macros all use %rdi as the single memory argument. */
#define XSAVEOPT        ".byte 0x48,0x0f,0xae,0x37"
#define XSAVES          ".byte 0x48,0x0f,0xc7,0x2f"
#define XRSTOR          ".byte 0x48,0x0f,0xae,0x2f"
#define XRSTORS         ".byte 0x48,0x0f,0xc7,0x1f"

static inline void xsaves(struct xregs_state *xstate, uint64_t mask)
{
        uint32_t lmask = mask, hmask = mask >> 32;

        asm volatile(XSAVES
                     : : "D" (xstate), "m" (*xstate), "a" (lmask), "d" (hmask)
                     : "memory");
}

static inline void xrstors(struct xregs_state *xstate, uint64_t mask)
{
        uint32_t lmask = mask, hmask = mask >> 32;

        asm volatile(XRSTORS
                     : : "D" (xstate), "m" (*xstate), "a" (lmask), "d" (hmask)
                     : "memory");
}

static inline void xsaveopt(struct xregs_state *xstate, uint64_t mask)
{
        uint32_t lmask = mask, hmask = mask >> 32;

        asm volatile(XSAVEOPT
                     : : "D" (xstate), "m" (*xstate), "a" (lmask), "d" (hmask)
                     : "memory");
}

static inline void xrstor(struct xregs_state *xstate, uint64_t mask)
{
        uint32_t lmask = mask, hmask = mask >> 32;

        asm volatile(XRSTOR
                     : : "D" (xstate), "m" (*xstate), "a" (lmask), "d" (hmask)
                     : "memory");
}

/* Save processor xstate to xsave area. */
void copy_xregs_to_kernel(void *xstate);
/* Restore processor xstate from xsave area. */
void copy_kernel_to_xregs(void *xstate);

extern size_t fpu_kernel_xstate_size;
extern union fpregs_state init_fpstate;
