#include <asm/apic.h>
#include <asm/cpu_entry_area.h>
#include <asm/irq.h>
#include <asm/setup.h>
#include <asm/traps.h>
#include <sys/bitops.h>

struct idt_data {
        unsigned int    vector;
        unsigned int    segment;
        struct idt_bits bits;
        const void      *addr;
};

#define DPL0            0x0
#define DPL3            0x3

#define DEFAULT_STACK   0

#define G(_vector, _addr, _ist, _type, _dpl, _segment)  \
        {                                               \
                .vector         = _vector,              \
                .bits.ist       = _ist,                 \
                .bits.type      = _type,                \
                .bits.dpl       = _dpl,                 \
                .bits.p         = 1,                    \
                .addr           = _addr,                \
                .segment        = _segment,             \
        }

/* Interrupt gate */
#define INTG(_vector, _addr)                            \
        G(_vector, _addr, DEFAULT_STACK, GATE_INTERRUPT, DPL0, KERNEL_CS)

/* System interrupt gate */
#define SYSG(_vector, _addr)                            \
        G(_vector, _addr, DEFAULT_STACK, GATE_INTERRUPT, DPL3, KERNEL_CS)

/* Interrupt gate with interrupt stack */
#define ISTG(_vector, _addr, _ist)                      \
        G(_vector, _addr, _ist, GATE_INTERRUPT, DPL0, KERNEL_CS)

/* System interrupt gate with interrupt stack */
#define SISTG(_vector, _addr, _ist)                     \
        G(_vector, _addr, _ist, GATE_INTERRUPT, DPL3, KERNEL_CS)

static const struct idt_data def_idts[] = {
        INTG(X86_TRAP_DE,               divide_error),
        INTG(X86_TRAP_BR,               bounds),
        INTG(X86_TRAP_UD,               invalid_op),
        INTG(X86_TRAP_NM,               device_not_available),
        INTG(X86_TRAP_OLD_MF,           coprocessor_segment_overrun),
        INTG(X86_TRAP_TS,               invalid_TSS),
        INTG(X86_TRAP_NP,               segment_not_present),
        INTG(X86_TRAP_SS,               stack_segment),
        INTG(X86_TRAP_GP,               general_protection),
        INTG(X86_TRAP_PF,               page_fault),
        INTG(X86_TRAP_SPURIOUS,         spurious_interrupt_bug),
        INTG(X86_TRAP_MF,               coprocessor_error),
        INTG(X86_TRAP_AC,               alignment_check),
        INTG(X86_TRAP_XF,               simd_coprocessor_error),
        INTG(X86_TRAP_DF,               double_fault),
        SYSG(X86_TRAP_BP,               int3),
        SYSG(X86_TRAP_OF,               overflow),
};

/*
 * The APIC and SMP idt entries
 */
static const struct idt_data apic_idts[] = {
        INTG(LOCAL_TIMER_VECTOR,        apic_timer_interrupt),
        INTG(SPURIOUS_APIC_VECTOR,      spurious_interrupt),
        INTG(ERROR_APIC_VECTOR,         error_interrupt),
};

/*
 * The following exceptions use Interrupt stacks.
 * They are setup after the TSS has been initialized.
 */
static const struct idt_data ist_idts[] = {
        ISTG(X86_TRAP_DF,       double_fault,   DOUBLEFAULT_STACK),
};

static struct gate_desc idt_table[IDT_ENTRIES] __aligned(PAGE_SIZE);

static struct desc_ptr idt_descr = {
        .size = IDT_ENTRIES * 16 - 1,
        .address = CPU_ENTRY_AREA_IDT,
};

static DECLARE_BITMAP(system_vectors, NR_VECTORS);

static inline void idt_init_desc(struct gate_desc *gate, const struct idt_data *d)
{
        const char *va = d->addr;
        uintptr_t addr;

        BUG_ON(va < __entry_text_start);
        BUG_ON(va >= __entry_text_end);
        addr = cpu_entry_area_text_address(va);

        gate->offset_low        = (uint16_t) addr;
        gate->segment           = (uint16_t) d->segment;
        gate->bits              = d->bits;
        gate->offset_middle     = (uint16_t) (addr >> 16);
        gate->offset_high       = (uint32_t) (addr >> 32);
        gate->reserved          = 0;
}

static void idt_setup_from_table(struct gate_desc *idt, const struct idt_data *t, int size, bool sys)
{
        struct gate_desc desc;

        for (; size > 0; t++, size--) {
                idt_init_desc(&desc, t);
                write_idt_entry(idt, t->vector, &desc);
                if (sys)
                        set_bit(t->vector, system_vectors);
        }
}

static void set_intr_gate(unsigned int n, const void *addr)
{
        struct idt_data data;

        BUG_ON(n > 0xFF);

        memset(&data, 0, sizeof(data));
        data.vector     = n;
        data.addr       = addr;
        data.segment    = KERNEL_CS;
        data.bits.type  = GATE_INTERRUPT;
        data.bits.p     = 1;

        idt_setup_from_table(idt_table, &data, 1, false);
}

/**
 * idt_setup_traps - Initialize the idt table with default traps
 */
void idt_setup_traps(void)
{
        size_t entry_text_size;

        idt_setup_from_table(idt_table, def_idts, ARRAY_SIZE(def_idts), true);

        load_idt(&idt_descr);

        cea_set_pte((void *)CPU_ENTRY_AREA_IDT, __pa(idt_table), PTE_KERNEL_RO);

        entry_text_size = __entry_text_end - __entry_text_start;
        BUG_ON(entry_text_size % PAGE_SIZE);
        cea_map_pages((void *)CPU_ENTRY_AREA_TEXT, __pa(__entry_text_start), entry_text_size / PAGE_SIZE, PTE_KERNEL_RX);
}

/**
 * idt_setup_ist_traps - Initialize the idt table with traps using IST
 */
void idt_setup_ist_traps(void)
{
        idt_setup_from_table(idt_table, ist_idts, ARRAY_SIZE(ist_idts), true);
}

void idt_setup_apic_and_irq_gates(void)
{
        int i = FIRST_EXTERNAL_VECTOR;

        idt_setup_from_table(idt_table, apic_idts, ARRAY_SIZE(apic_idts), true);

        for_each_clear_bit_from(i, system_vectors, NR_VECTORS) {
                set_bit(i, system_vectors);
                set_intr_gate(i, spurious_interrupt);
        }
}

void update_intr_gate(unsigned int n, const void *addr)
{
        BUG_ON(!test_bit(n, system_vectors));
        set_intr_gate(n, addr);
}

__weak void do_trap(struct pt_regs *regs, long error_code, char *str, unsigned long trapnr)
{
        pr_err("unknown vector: %ld (%s)\n", trapnr, str);
        show_regs(regs);
        die();
}

#define DO_ERROR(trapnr, str, name)                             \
__weak void do_##name(struct pt_regs *regs, long error_code)    \
{                                                               \
        do_trap(regs, error_code, str, trapnr);                 \
}

DO_ERROR(X86_TRAP_DE,     "divide error",               divide_error)
DO_ERROR(X86_TRAP_BP,     "int3",                       int3)
DO_ERROR(X86_TRAP_OF,     "overflow",                   overflow)
DO_ERROR(X86_TRAP_BR,     "bounds",                     bounds)
DO_ERROR(X86_TRAP_UD,     "invalid opcode",             invalid_op)
DO_ERROR(X86_TRAP_NM,     "device not available",       device_not_available)
DO_ERROR(X86_TRAP_DF,     "double fault",               double_fault)
DO_ERROR(X86_TRAP_OLD_MF, "coprocessor segment overrun",coprocessor_segment_overrun)
DO_ERROR(X86_TRAP_TS,     "invalid TSS",                invalid_TSS)
DO_ERROR(X86_TRAP_NP,     "segment not present",        segment_not_present)
DO_ERROR(X86_TRAP_SS,     "stack segment",              stack_segment)
DO_ERROR(X86_TRAP_GP,     "general protection fault",   general_protection)
DO_ERROR(X86_TRAP_PF,     "page fault",                 page_fault)
DO_ERROR(X86_TRAP_MF,     "coprocessor error",          coprocessor_error)
DO_ERROR(X86_TRAP_AC,     "alignment check",            alignment_check)
DO_ERROR(X86_TRAP_XF,     "SIMD coprocessor error",     simd_coprocessor_error)

__weak void do_spurious_interrupt_bug(struct pt_regs *regs, long error_code)
{
}

__weak void smp_apic_timer_interrupt(struct pt_regs *regs)
{
        apic_eoi();
}

__weak void smp_spurious_interrupt(struct pt_regs *regs)
{
        BUG_ON("TBD");
}

/*
 * This interrupt should never happen with our APIC/SMP architecture
 */
__weak void smp_error_interrupt(struct pt_regs *regs)
{
        static const char * const error_interrupt_reason[] = {
                "Send CS error",                /* APIC Error Bit 0 */
                "Receive CS error",             /* APIC Error Bit 1 */
                "Send accept error",            /* APIC Error Bit 2 */
                "Receive accept error",         /* APIC Error Bit 3 */
                "Redirectable IPI",             /* APIC Error Bit 4 */
                "Send illegal vector",          /* APIC Error Bit 5 */
                "Received illegal vector",      /* APIC Error Bit 6 */
                "Illegal register address",     /* APIC Error Bit 7 */
        };
        uint32_t v, i = 0;

        apic_write(APIC_ESR, 0);
        v = apic_read(APIC_ESR);
        apic_eoi();

        pr_info("APIC error on CPU%d: %02x", smp_processor_id(), v);

        v &= 0xff;
        while (v) {
                if (v & 0x1)
                        pr_cont(" : %s", error_interrupt_reason[i]);
                i++;
                v >>= 1;
        }

        pr_cont("\n");
}
