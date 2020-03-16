#pragma once

#include <asm/segment.h>
#include <sys/percpu.h>
#include <sys/string.h>

/* 8-byte segment */
struct segment_desc {
        uint16_t limit0;
        uint16_t base0;
        uint16_t base1: 8, type: 4, s: 1, dpl: 2, p: 1;
        uint16_t limit1: 4, avl: 1, l: 1, d: 1, g: 1, base2: 8;
} __packed;

#define GDT_ENTRY_INIT(flags, base, limit)                      \
        {                                                       \
                .limit0         = (uint16_t) (limit),           \
                .limit1         = ((limit) >> 16) & 0x0F,       \
                .base0          = (uint16_t) (base),            \
                .base1          = ((base) >> 16) & 0xFF,        \
                .base2          = ((base) >> 24) & 0xFF,        \
                .type           = (flags & 0x0f),               \
                .s              = (flags >> 4) & 0x01,          \
                .dpl            = (flags >> 5) & 0x03,          \
                .p              = (flags >> 7) & 0x01,          \
                .avl            = (flags >> 12) & 0x01,         \
                .l              = (flags >> 13) & 0x01,         \
                .d              = (flags >> 14) & 0x01,         \
                .g              = (flags >> 15) & 0x01,         \
        }

enum {
        GATE_INTERRUPT = 0xE,
        GATE_TRAP = 0xF,
        GATE_CALL = 0xC,
        GATE_TASK = 0x5,
};

enum {
        DESC_TSS = 0x9,
        DESC_LDT = 0x2,
        DESCTYPE_S = 0x10,      /* !system */
};

struct ldttss_desc {
        uint16_t        limit0;
        uint16_t        base0;

        uint16_t        base1 : 8, type : 5, dpl : 2, p : 1;
        uint16_t        limit1 : 4, zero0 : 3, g : 1, base2 : 8;
        uint32_t        base3;
        uint32_t        zero1;
} __packed;

#define ldt_desc ldttss_desc
#define tss_desc ldttss_desc

struct idt_bits {
        uint16_t        ist     : 3,
                        zero    : 5,
                        type    : 5,
                        dpl     : 2,
                        p       : 1;
} __packed;

struct gate_desc {
        uint16_t        offset_low;
        uint16_t        segment;
        struct idt_bits bits;
        uint16_t        offset_middle;
        uint32_t        offset_high;
        uint32_t        reserved;
} __packed;

struct desc_ptr {
        unsigned short size;
        unsigned long address;
} __packed;

static inline void load_gdt(const struct desc_ptr *dtr)
{
        asm volatile("lgdt %0" : : "m" (*dtr));
}

static inline void load_idt(const struct desc_ptr *dtr)
{
        asm volatile("lidt %0" : : "m" (*dtr));
}

static inline void store_gdt(struct desc_ptr *dtr)
{
        asm volatile("sgdt %0" : "=m" (*dtr));
}

static inline void store_idt(struct desc_ptr *dtr)
{
        asm volatile("sidt %0" : "=m" (*dtr));
}

static inline void write_idt_entry(struct gate_desc *idt, int entry, const struct gate_desc *gate)
{
        memcpy(&idt[entry], gate, sizeof(*gate));
}

static inline void write_gdt_entry(struct segment_desc *gdt, int entry, const void *desc, int type)
{
        size_t size;

        switch (type) {
        case DESC_TSS:  size = sizeof(struct ldttss_desc);      break;
        case DESC_LDT:  size = sizeof(struct ldttss_desc);      break;
        default:        size = sizeof(*gdt);                    break;
        }

        memcpy(&gdt[entry], desc, size);
}

static inline void set_tssldt_descriptor(struct tss_desc *desc, unsigned long addr, unsigned type, unsigned size)
{
        memset(desc, 0, sizeof(*desc));

        desc->limit0            = (uint16_t) size;
        desc->base0             = (uint16_t) addr;
        desc->base1             = (addr >> 16) & 0xFF;
        desc->type              = type;
        desc->p                 = 1;
        desc->limit1            = (size >> 16) & 0xF;
        desc->base2             = (addr >> 24) & 0xFF;
        desc->base3             = (uint32_t) (addr >> 32);
}

struct segment_desc *get_cpu_gdt_ro(int cpu);
struct segment_desc *get_cpu_gdt_rw(int cpu);
void load_tr_desc(void);

static inline struct segment_desc *get_current_gdt_rw(void)
{
        return get_cpu_gdt_rw(smp_processor_id());
}

struct pt_regs *get_cpu_pt_regs(int cpu);

static inline struct pt_regs *get_current_pt_regs(void)
{
        return get_cpu_pt_regs(smp_processor_id());
}

void idt_setup_traps(void);
void idt_setup_ist_traps(void);
void idt_setup_apic_and_irq_gates(void);
