#include <asm/apic.h>
#include <asm/processor.h>
#include <sys/delay.h>

uint64_t acpi_lapic_addr = APIC_DEFAULT_PHYS_BASE;

static void xapic_init_apic_ldr(void)
{
        unsigned long num, id, val;

        num = smp_processor_id();
        id = 1UL << num;
        apic_write(APIC_DFR, APIC_DFR_FLAT);
        val = apic_read(APIC_LDR) & ~APIC_LDR_MASK;
        val |= SET_APIC_LOGICAL_ID(id);
        apic_write(APIC_LDR, val);
}

static unsigned int xapic_get_apic_id(unsigned long x)
{
        return (x >> 24) & 0xFF;
}

static inline uint32_t xapic_read(uint32_t reg)
{
        return *((volatile uint32_t *)(acpi_lapic_addr + reg));
}

static inline void xapic_write(uint32_t reg, uint32_t v)
{
        volatile uint32_t *addr = (volatile uint32_t *)(acpi_lapic_addr + reg);

        *addr = v;
}

static uint64_t xapic_icr_read(void)
{
        uint32_t icr1, icr2;

        icr2 = apic_read(APIC_ICR2);
        icr1 = apic_read(APIC_ICR);
        return icr1 | ((uint64_t)icr2 << 32);
}

static void xapic_icr_write(uint32_t low, uint32_t id)
{
        apic_write(APIC_ICR2, SET_APIC_DEST_FIELD(id));
        apic_write(APIC_ICR, low);
}

static uint32_t xapic_safe_wait_icr_idle(void)
{
        uint32_t send_status;
        int timeout;

        timeout = 0;
        do {
                send_status = apic_read(APIC_ICR) & APIC_ICR_BUSY;
                if (!send_status)
                        break;
                udelay(100);
        } while (timeout++ < 1000);

        return send_status;
}

struct apic xapic = {
        .eoi_write = xapic_write,
        .init_apic_ldr = xapic_init_apic_ldr,
        .get_apic_id = xapic_get_apic_id,
        .read = xapic_read,
        .write = xapic_write,
        .icr_read = xapic_icr_read,
        .icr_write = xapic_icr_write,
        .safe_wait_icr_idle = xapic_safe_wait_icr_idle,
};
