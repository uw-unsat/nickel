#pragma once

#include <asm/processor-flags.h>
#include <sys/types.h>

enum {
        INTERCEPT_INTR,
        INTERCEPT_NMI,
        INTERCEPT_SMI,
        INTERCEPT_INIT,
        INTERCEPT_VINTR,
        INTERCEPT_SELECTIVE_CR0,
        INTERCEPT_STORE_IDTR,
        INTERCEPT_STORE_GDTR,
        INTERCEPT_STORE_LDTR,
        INTERCEPT_STORE_TR,
        INTERCEPT_LOAD_IDTR,
        INTERCEPT_LOAD_GDTR,
        INTERCEPT_LOAD_LDTR,
        INTERCEPT_LOAD_TR,
        INTERCEPT_RDTSC,
        INTERCEPT_RDPMC,
        INTERCEPT_PUSHF,
        INTERCEPT_POPF,
        INTERCEPT_CPUID,
        INTERCEPT_RSM,
        INTERCEPT_IRET,
        INTERCEPT_INTn,
        INTERCEPT_INVD,
        INTERCEPT_PAUSE,
        INTERCEPT_HLT,
        INTERCEPT_INVLPG,
        INTERCEPT_INVLPGA,
        INTERCEPT_IOIO_PROT,
        INTERCEPT_MSR_PROT,
        INTERCEPT_TASK_SWITCH,
        INTERCEPT_FERR_FREEZE,
        INTERCEPT_SHUTDOWN,
        INTERCEPT_VMRUN,
        INTERCEPT_VMMCALL,
        INTERCEPT_VMLOAD,
        INTERCEPT_VMSAVE,
        INTERCEPT_STGI,
        INTERCEPT_CLGI,
        INTERCEPT_SKINIT,
        INTERCEPT_RDTSCP,
        INTERCEPT_ICEBP,
        INTERCEPT_WBINVD,
        INTERCEPT_MONITOR,
        INTERCEPT_MWAIT,
        INTERCEPT_MWAIT_COND,
        INTERCEPT_XSETBV,
};

struct vmcb_control_area {
        uint32_t intercept_cr;
        uint32_t intercept_dr;
        uint32_t intercept_exceptions;
        uint64_t intercept;
        uint8_t reserved_1[42];
        uint16_t pause_filter_count;
        uint64_t iopm_base_pa;
        uint64_t msrpm_base_pa;
        uint64_t tsc_offset;
        uint32_t asid;
        uint8_t tlb_ctl;
        uint8_t reserved_2[3];
        uint32_t int_ctl;
        uint32_t int_vector;
        uint32_t int_state;
        uint8_t reserved_3[4];
        uint32_t exit_code;
        uint32_t exit_code_hi;
        uint64_t exit_info_1;
        uint64_t exit_info_2;
        uint32_t exit_int_info;
        uint32_t exit_int_info_err;
        uint64_t nested_ctl;
        uint64_t avic_vapic_bar;
        uint8_t reserved_4[8];
        uint32_t event_inj;
        uint32_t event_inj_err;
        uint64_t nested_cr3;
        uint64_t lbr_ctl;
        uint32_t clean;
        uint32_t reserved_5;
        uint64_t next_rip;
        uint8_t insn_len;
        uint8_t insn_bytes[15];
        uint64_t avic_backing_page;     /* Offset 0xe0 */
        uint8_t reserved_6[8];  /* Offset 0xe8 */
        uint64_t avic_logical_id;       /* Offset 0xf0 */
        uint64_t avic_physical_id;      /* Offset 0xf8 */
        uint8_t reserved_7[768];
} __packed;

#define TLB_CONTROL_DO_NOTHING 0
#define TLB_CONTROL_FLUSH_ALL_ASID 1
#define TLB_CONTROL_FLUSH_ASID 3
#define TLB_CONTROL_FLUSH_ASID_LOCAL 7

#define V_TPR_MASK 0x0f

#define V_IRQ_SHIFT 8
#define V_IRQ_MASK (1 << V_IRQ_SHIFT)

#define V_INTR_PRIO_SHIFT 16
#define V_INTR_PRIO_MASK (0x0f << V_INTR_PRIO_SHIFT)

#define V_IGN_TPR_SHIFT 20
#define V_IGN_TPR_MASK (1 << V_IGN_TPR_SHIFT)

#define V_INTR_MASKING_SHIFT 24
#define V_INTR_MASKING_MASK (1 << V_INTR_MASKING_SHIFT)

#define AVIC_ENABLE_SHIFT 31
#define AVIC_ENABLE_MASK (1 << AVIC_ENABLE_SHIFT)

#define SVM_INTERRUPT_SHADOW_MASK 1

#define SVM_IOIO_STR_SHIFT 2
#define SVM_IOIO_REP_SHIFT 3
#define SVM_IOIO_SIZE_SHIFT 4
#define SVM_IOIO_ASIZE_SHIFT 7

#define SVM_IOIO_TYPE_MASK 1
#define SVM_IOIO_STR_MASK (1 << SVM_IOIO_STR_SHIFT)
#define SVM_IOIO_REP_MASK (1 << SVM_IOIO_REP_SHIFT)
#define SVM_IOIO_SIZE_MASK (7 << SVM_IOIO_SIZE_SHIFT)
#define SVM_IOIO_ASIZE_MASK (7 << SVM_IOIO_ASIZE_SHIFT)

#define SVM_VM_CR_VALID_MASK    0x001fULL
#define SVM_VM_CR_SVM_LOCK_MASK 0x0008ULL
#define SVM_VM_CR_SVM_DIS_MASK  0x0010ULL

struct vmcb_seg {
        uint16_t selector;
        uint16_t attrib;
        uint32_t limit;
        uint64_t base;
} __packed;

struct vmcb_save_area {
        struct vmcb_seg es;
        struct vmcb_seg cs;
        struct vmcb_seg ss;
        struct vmcb_seg ds;
        struct vmcb_seg fs;
        struct vmcb_seg gs;
        struct vmcb_seg gdtr;
        struct vmcb_seg ldtr;
        struct vmcb_seg idtr;
        struct vmcb_seg tr;
        uint8_t reserved_1[43];
        uint8_t cpl;
        uint8_t reserved_2[4];
        uint64_t efer;
        uint8_t reserved_3[112];
        uint64_t cr4;
        uint64_t cr3;
        uint64_t cr0;
        uint64_t dr7;
        uint64_t dr6;
        uint64_t rflags;
        uint64_t rip;
        uint8_t reserved_4[88];
        uint64_t rsp;
        uint8_t reserved_5[24];
        uint64_t rax;
        uint64_t star;
        uint64_t lstar;
        uint64_t cstar;
        uint64_t sfmask;
        uint64_t kernel_gs_base;
        uint64_t sysenter_cs;
        uint64_t sysenter_esp;
        uint64_t sysenter_eip;
        uint64_t cr2;
        uint8_t reserved_6[32];
        uint64_t g_pat;
        uint64_t dbgctl;
        uint64_t br_from;
        uint64_t br_to;
        uint64_t last_excp_from;
        uint64_t last_excp_to;
} __packed;

struct vmcb {
        struct vmcb_control_area control;
        struct vmcb_save_area save;
} __packed;

#define SVM_CPUID_FUNC          0x8000000a

#define SVM_VM_CR_SVM_DISABLE   4

#define SVM_SELECTOR_S_SHIFT    4
#define SVM_SELECTOR_DPL_SHIFT  5
#define SVM_SELECTOR_P_SHIFT    7
#define SVM_SELECTOR_AVL_SHIFT  8
#define SVM_SELECTOR_L_SHIFT    9
#define SVM_SELECTOR_DB_SHIFT   10
#define SVM_SELECTOR_G_SHIFT    11

#define SVM_SELECTOR_TYPE_MASK  (0xf)
#define SVM_SELECTOR_S_MASK     (1 << SVM_SELECTOR_S_SHIFT)
#define SVM_SELECTOR_DPL_MASK   (3 << SVM_SELECTOR_DPL_SHIFT)
#define SVM_SELECTOR_P_MASK     (1 << SVM_SELECTOR_P_SHIFT)
#define SVM_SELECTOR_AVL_MASK   (1 << SVM_SELECTOR_AVL_SHIFT)
#define SVM_SELECTOR_L_MASK     (1 << SVM_SELECTOR_L_SHIFT)
#define SVM_SELECTOR_DB_MASK    (1 << SVM_SELECTOR_DB_SHIFT)
#define SVM_SELECTOR_G_MASK     (1 << SVM_SELECTOR_G_SHIFT)

#define SVM_SELECTOR_WRITE_MASK (1 << 1)
#define SVM_SELECTOR_READ_MASK  SVM_SELECTOR_WRITE_MASK
#define SVM_SELECTOR_CODE_MASK  (1 << 3)

#define INTERCEPT_CR0_READ      0
#define INTERCEPT_CR3_READ      3
#define INTERCEPT_CR4_READ      4
#define INTERCEPT_CR8_READ      8
#define INTERCEPT_CR0_WRITE     (16 + 0)
#define INTERCEPT_CR3_WRITE     (16 + 3)
#define INTERCEPT_CR4_WRITE     (16 + 4)
#define INTERCEPT_CR8_WRITE     (16 + 8)

#define INTERCEPT_DR0_READ      0
#define INTERCEPT_DR1_READ      1
#define INTERCEPT_DR2_READ      2
#define INTERCEPT_DR3_READ      3
#define INTERCEPT_DR4_READ      4
#define INTERCEPT_DR5_READ      5
#define INTERCEPT_DR6_READ      6
#define INTERCEPT_DR7_READ      7
#define INTERCEPT_DR0_WRITE     (16 + 0)
#define INTERCEPT_DR1_WRITE     (16 + 1)
#define INTERCEPT_DR2_WRITE     (16 + 2)
#define INTERCEPT_DR3_WRITE     (16 + 3)
#define INTERCEPT_DR4_WRITE     (16 + 4)
#define INTERCEPT_DR5_WRITE     (16 + 5)
#define INTERCEPT_DR6_WRITE     (16 + 6)
#define INTERCEPT_DR7_WRITE     (16 + 7)

#define SVM_EVTINJ_VEC_MASK     0xff

#define SVM_EVTINJ_TYPE_SHIFT   8
#define SVM_EVTINJ_TYPE_MASK    (7 << SVM_EVTINJ_TYPE_SHIFT)

#define SVM_EVTINJ_TYPE_INTR    (0 << SVM_EVTINJ_TYPE_SHIFT)
#define SVM_EVTINJ_TYPE_NMI     (2 << SVM_EVTINJ_TYPE_SHIFT)
#define SVM_EVTINJ_TYPE_EXEPT   (3 << SVM_EVTINJ_TYPE_SHIFT)
#define SVM_EVTINJ_TYPE_SOFT    (4 << SVM_EVTINJ_TYPE_SHIFT)

#define SVM_EVTINJ_VALID        (1 << 31)
#define SVM_EVTINJ_VALID_ERR    (1 << 11)

#define SVM_EXITINTINFO_VEC_MASK        SVM_EVTINJ_VEC_MASK
#define SVM_EXITINTINFO_TYPE_MASK       SVM_EVTINJ_TYPE_MASK

#define SVM_EXITINTINFO_TYPE_INTR       SVM_EVTINJ_TYPE_INTR
#define SVM_EXITINTINFO_TYPE_NMI        SVM_EVTINJ_TYPE_NMI
#define SVM_EXITINTINFO_TYPE_EXEPT      SVM_EVTINJ_TYPE_EXEPT
#define SVM_EXITINTINFO_TYPE_SOFT       SVM_EVTINJ_TYPE_SOFT

#define SVM_EXITINTINFO_VALID           SVM_EVTINJ_VALID
#define SVM_EXITINTINFO_VALID_ERR       SVM_EVTINJ_VALID_ERR

#define SVM_EXITINFOSHIFT_TS_REASON_IRET        36
#define SVM_EXITINFOSHIFT_TS_REASON_JMP         38
#define SVM_EXITINFOSHIFT_TS_HAS_ERROR_CODE     44

#define SVM_EXITINFO_REG_MASK   0x0F

#define SVM_CR0_SELECTIVE_MASK  (X86_CR0_TS | X86_CR0_MP)

#define SVM_EXIT_READ_CR0      0x000
#define SVM_EXIT_READ_CR2      0x002
#define SVM_EXIT_READ_CR3      0x003
#define SVM_EXIT_READ_CR4      0x004
#define SVM_EXIT_READ_CR8      0x008
#define SVM_EXIT_WRITE_CR0     0x010
#define SVM_EXIT_WRITE_CR2     0x012
#define SVM_EXIT_WRITE_CR3     0x013
#define SVM_EXIT_WRITE_CR4     0x014
#define SVM_EXIT_WRITE_CR8     0x018
#define SVM_EXIT_READ_DR0      0x020
#define SVM_EXIT_READ_DR1      0x021
#define SVM_EXIT_READ_DR2      0x022
#define SVM_EXIT_READ_DR3      0x023
#define SVM_EXIT_READ_DR4      0x024
#define SVM_EXIT_READ_DR5      0x025
#define SVM_EXIT_READ_DR6      0x026
#define SVM_EXIT_READ_DR7      0x027
#define SVM_EXIT_WRITE_DR0     0x030
#define SVM_EXIT_WRITE_DR1     0x031
#define SVM_EXIT_WRITE_DR2     0x032
#define SVM_EXIT_WRITE_DR3     0x033
#define SVM_EXIT_WRITE_DR4     0x034
#define SVM_EXIT_WRITE_DR5     0x035
#define SVM_EXIT_WRITE_DR6     0x036
#define SVM_EXIT_WRITE_DR7     0x037
#define SVM_EXIT_EXCP_BASE     0x040
#define SVM_EXIT_INTR          0x060
#define SVM_EXIT_NMI           0x061
#define SVM_EXIT_SMI           0x062
#define SVM_EXIT_INIT          0x063
#define SVM_EXIT_VINTR         0x064
#define SVM_EXIT_CR0_SEL_WRITE 0x065
#define SVM_EXIT_IDTR_READ     0x066
#define SVM_EXIT_GDTR_READ     0x067
#define SVM_EXIT_LDTR_READ     0x068
#define SVM_EXIT_TR_READ       0x069
#define SVM_EXIT_IDTR_WRITE    0x06a
#define SVM_EXIT_GDTR_WRITE    0x06b
#define SVM_EXIT_LDTR_WRITE    0x06c
#define SVM_EXIT_TR_WRITE      0x06d
#define SVM_EXIT_RDTSC         0x06e
#define SVM_EXIT_RDPMC         0x06f
#define SVM_EXIT_PUSHF         0x070
#define SVM_EXIT_POPF          0x071
#define SVM_EXIT_CPUID         0x072
#define SVM_EXIT_RSM           0x073
#define SVM_EXIT_IRET          0x074
#define SVM_EXIT_SWINT         0x075
#define SVM_EXIT_INVD          0x076
#define SVM_EXIT_PAUSE         0x077
#define SVM_EXIT_HLT           0x078
#define SVM_EXIT_INVLPG        0x079
#define SVM_EXIT_INVLPGA       0x07a
#define SVM_EXIT_IOIO          0x07b
#define SVM_EXIT_MSR           0x07c
#define SVM_EXIT_TASK_SWITCH   0x07d
#define SVM_EXIT_FERR_FREEZE   0x07e
#define SVM_EXIT_SHUTDOWN      0x07f
#define SVM_EXIT_VMRUN         0x080
#define SVM_EXIT_VMMCALL       0x081
#define SVM_EXIT_VMLOAD        0x082
#define SVM_EXIT_VMSAVE        0x083
#define SVM_EXIT_STGI          0x084
#define SVM_EXIT_CLGI          0x085
#define SVM_EXIT_SKINIT        0x086
#define SVM_EXIT_RDTSCP        0x087
#define SVM_EXIT_ICEBP         0x088
#define SVM_EXIT_WBINVD        0x089
#define SVM_EXIT_MONITOR       0x08a
#define SVM_EXIT_MWAIT         0x08b
#define SVM_EXIT_MWAIT_COND    0x08c
#define SVM_EXIT_XSETBV        0x08d
#define SVM_EXIT_NPF           0x400
#define SVM_EXIT_AVIC_INCOMPLETE_IPI            0x401
#define SVM_EXIT_AVIC_UNACCELERATED_ACCESS      0x402

#define SVM_EXIT_ERR           -1
