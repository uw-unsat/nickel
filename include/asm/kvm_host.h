#pragma once

#include <asm/kvm_types.h>

enum kvm_reg {
        VCPU_REGS_RAX = 0,
        VCPU_REGS_RCX = 1,
        VCPU_REGS_RDX = 2,
        VCPU_REGS_RBX = 3,
        VCPU_REGS_RSP = 4,
        VCPU_REGS_RBP = 5,
        VCPU_REGS_RSI = 6,
        VCPU_REGS_RDI = 7,
        VCPU_REGS_R8 = 8,
        VCPU_REGS_R9 = 9,
        VCPU_REGS_R10 = 10,
        VCPU_REGS_R11 = 11,
        VCPU_REGS_R12 = 12,
        VCPU_REGS_R13 = 13,
        VCPU_REGS_R14 = 14,
        VCPU_REGS_R15 = 15,
        VCPU_REGS_RIP,
        NR_VCPU_REGS
};

enum {
        VCPU_SREG_ES,
        VCPU_SREG_CS,
        VCPU_SREG_SS,
        VCPU_SREG_DS,
        VCPU_SREG_FS,
        VCPU_SREG_GS,
        VCPU_SREG_TR,
        VCPU_SREG_LDTR,
};

enum {
        ACTIVITY_STATE_ACTIVE = 0,
        ACTIVITY_STATE_HLT,
        ACTIVITY_STATE_SHUTDOWN,
        ACTIVITY_STATE_WAIT_FOR_SIPI,
};

#define PFERR_PRESENT_BIT       0
#define PFERR_WRITE_BIT         1
#define PFERR_USER_BIT          2
#define PFERR_RSVD_BIT          3
#define PFERR_FETCH_BIT         4
#define PFERR_PK_BIT            5
#define PFERR_GUEST_FINAL_BIT   32
#define PFERR_GUEST_PAGE_BIT    33

#define PFERR_PRESENT_MASK      BIT_64(PFERR_PRESENT_BIT)
#define PFERR_WRITE_MASK        BIT_64(PFERR_WRITE_BIT)
#define PFERR_USER_MASK         BIT_64(PFERR_USER_BIT)
#define PFERR_RSVD_MASK         BIT_64(PFERR_RSVD_BIT)
#define PFERR_FETCH_MASK        BIT_64(PFERR_FETCH_BIT)
#define PFERR_PK_MASK           BIT_64(PFERR_PK_BIT)
#define PFERR_GUEST_FINAL_MASK  BIT_64(PFERR_GUEST_FINAL_BIT)
#define PFERR_GUEST_PAGE_MASK   BIT_64(PFERR_GUEST_PAGE_BIT)

struct kvm_vcpu {
        uint64_t regs[NR_VCPU_REGS];
        uint64_t cr2;
        _Atomic int activity_state;
        uint8_t sipi_vector;
};

struct msr_data {
        bool host_initiated;
        uint32_t index;
        uint64_t data;
};

struct kvm_x86_ops {
        int (*cpu_has_kvm_support)(void);
        int (*disabled_by_bios)(void);
        int (*hardware_setup)(void);

        struct kvm_vcpu *(*vcpu_enable)(void);
        void (*vcpu_setup)(struct kvm_vcpu *vcpu);

        void (*set_tdp)(struct kvm_vcpu *vcpu, unsigned long tdp);
        void (*set_exception_bitmap)(struct kvm_vcpu *vcpu, uint32_t exception_bitmap);

        int (*get_msr)(struct kvm_vcpu *vcpu, struct msr_data *msr);
        int (*set_msr)(struct kvm_vcpu *vcpu, struct msr_data *msr);
        int (*get_cpl)(struct kvm_vcpu *vcpu);
        unsigned long (*get_cr3)(struct kvm_vcpu *vcpu);
        void (*get_segment)(struct kvm_vcpu *vcpu, struct kvm_segment *var, int seg);
        void (*set_segment)(struct kvm_vcpu *vcpu, struct kvm_segment *var, int seg);
        void (*get_idt)(struct kvm_vcpu *vcpu, struct desc_ptr *dt);
        void (*set_idt)(struct kvm_vcpu *vcpu, struct desc_ptr *dt);
        unsigned long (*get_rflags)(struct kvm_vcpu *vcpu);
        void (*set_rflags)(struct kvm_vcpu *vcpu, unsigned long rflags);

        uint64_t (*get_efer)(struct kvm_vcpu *vcpu);
        void (*set_efer)(struct kvm_vcpu *vcpu, uint64_t efer);

        void (*run)(struct kvm_vcpu *vcpu);
        void (*handle_exit)(struct kvm_vcpu *vcpu);
        void (*skip_emulated_instruction)(struct kvm_vcpu *vcpu);

        void (*inject_exception)(struct kvm_vcpu *vcpu, uint8_t nr, bool has_error_code, uint32_t error_code);
};

static inline unsigned long kvm_register_read(struct kvm_vcpu *vcpu,
                                              enum kvm_reg reg)
{
        return vcpu->regs[reg];
}

static inline uint64_t kvm_read_edx_eax(struct kvm_vcpu *vcpu)
{
        uint32_t eax = kvm_register_read(vcpu, VCPU_REGS_RAX);
        uint32_t edx = kvm_register_read(vcpu, VCPU_REGS_RDX);

        return eax | ((uint64_t)edx << 32);
}

static inline void kvm_register_write(struct kvm_vcpu *vcpu,
                                      enum kvm_reg reg,
                                      unsigned long val)
{
        vcpu->regs[reg] = val;
}

static inline void kvm_write_edx_eax(struct kvm_vcpu *vcpu, uint64_t val)
{
        kvm_register_write(vcpu, VCPU_REGS_RAX, (uint32_t)val);
        kvm_register_write(vcpu, VCPU_REGS_RDX, (uint32_t)(val >> 32));
}

static inline void kvm_boot_ap(struct kvm_vcpu *vcpu, uint8_t sipi_vector)
{
        /* set SIPI vector */
        vcpu->sipi_vector = sipi_vector;
        /* wake up AP */
        atomic_store(&vcpu->activity_state, ACTIVITY_STATE_ACTIVE);
}

static inline unsigned long kvm_rip_read(struct kvm_vcpu *vcpu)
{
        return kvm_register_read(vcpu, VCPU_REGS_RIP);
}

static inline void kvm_rip_write(struct kvm_vcpu *vcpu, unsigned long val)
{
        kvm_register_write(vcpu, VCPU_REGS_RIP, val);
}

void kvm_get_idt(struct kvm_vcpu *vcpu, struct desc_ptr *dt);
void kvm_set_idt(struct kvm_vcpu *vcpu, struct desc_ptr *dt);

unsigned long kvm_rflags_read(struct kvm_vcpu *vcpu);
void kvm_rflags_write(struct kvm_vcpu *vcpu, unsigned long val);

int kvm_get_msr(struct kvm_vcpu *vcpu, struct msr_data *msr);
int kvm_set_msr(struct kvm_vcpu *vcpu, struct msr_data *msr);

int kvm_get_cpl(struct kvm_vcpu *vcpu);

static inline bool kvm_is_user_mode(struct kvm_vcpu *vcpu)
{
        return kvm_get_cpl(vcpu) == 3;
}

static inline bool kvm_is_kernel_mode(struct kvm_vcpu *vcpu)
{
        return kvm_get_cpl(vcpu) == 0;
}

unsigned long kvm_get_cr3(struct kvm_vcpu *vcpu);

void kvm_get_segment(struct kvm_vcpu *vcpu, struct kvm_segment *var, int seg);
void kvm_set_segment(struct kvm_vcpu *vcpu, struct kvm_segment *var, int seg);

void kvm_set_tdp(struct kvm_vcpu *vcpu, void *tdp);
void kvm_set_exception_bitmap(struct kvm_vcpu *vcpu, uint32_t exception_bitmap);

void kvm_emulate_cpuid(struct kvm_vcpu *vcpu);
void kvm_emulate_xsetbv(struct kvm_vcpu *vcpu);
void __kvm_emulate_hypercall(struct kvm_vcpu *vcpu);
void kvm_emulate_hypercall(struct kvm_vcpu *vcpu);
void kvm_skip_emulated_instruction(struct kvm_vcpu *vcpu);
void kvm_handle_tdp_fault(struct kvm_vcpu *vcpu, uint64_t error_code, gpa_t gpa);
void kvm_handle_exception(struct kvm_vcpu *vcpu, int trapnr, uint64_t error_code, gva_t fault_address);

void kvm_inject_exception(struct kvm_vcpu *vcpu, uint8_t nr, bool has_error_code, uint32_t error_code);

noreturn void kvm_loop(struct kvm_vcpu *vcpu);

struct kvm_vcpu *kvm_get_current_vcpu(void);
