#include <asm/apic.h>
#include <asm/msr.h>
#include <asm/processor.h>

static void x2apic_eoi_write(uint32_t reg, uint32_t v)
{
        wrmsr(APIC_BASE_MSR + (APIC_EOI >> 4), APIC_EOI_ACK, 0);
}

static void x2apic_init_apic_ldr(void)
{
}

static unsigned int x2apic_get_apic_id(unsigned long id)
{
        return id;
}

static inline uint32_t x2apic_read(uint32_t reg)
{
        if (reg == APIC_DFR)
                return -1;
        return (uint32_t)rdmsrl(APIC_BASE_MSR + (reg >> 4));
}

static inline void x2apic_write(uint32_t reg, uint32_t v)
{
        switch (reg) {
        case APIC_DFR:
        case APIC_ID:
        case APIC_LDR:
        case APIC_LVR:
                return;
        default:
                wrmsr(APIC_BASE_MSR + (reg >> 4), v, 0);
                break;
        }
}

static uint64_t x2apic_icr_read(void)
{
        return rdmsrl(APIC_BASE_MSR + (APIC_ICR >> 4));
}

static void x2apic_icr_write(uint32_t low, uint32_t id)
{
        wrmsrl(APIC_BASE_MSR + (APIC_ICR >> 4), ((uint64_t)id) << 32 | low);
}

static uint32_t x2apic_safe_wait_icr_idle(void)
{
        /* no need to wait for icr idle in x2apic */
        return 0;
}

struct apic x2apic = {
        .eoi_write = x2apic_eoi_write,
        .init_apic_ldr = x2apic_init_apic_ldr,
        .get_apic_id = x2apic_get_apic_id,
        .read = x2apic_read,
        .write = x2apic_write,
        .icr_read = x2apic_icr_read,
        .icr_write = x2apic_icr_write,
        .safe_wait_icr_idle = x2apic_safe_wait_icr_idle,
};
