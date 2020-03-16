#define pr_fmt(fmt) __MODULE__ ": " fmt

#include <asm/apic.h>
#include <asm/barrier.h>
#include <asm/processor.h>
#include <asm/rtc.h>
#include <asm/setup.h>
#include <asm/smp.h>
#include <sys/delay.h>
#include <sys/string.h>

#define TRAMPOLINE_STATUS_STARTED       0xA5A5A5A5

static _Atomic uint32_t trampoline_status;

static void cpu_up(int cpu, unsigned long start_ip);

void smp_init(uint32_t addr)
{
        extern char _binary_trampoline_start[], _binary_trampoline_end[];
        size_t _binary_trampoline_size = _binary_trampoline_end - _binary_trampoline_start;
        unsigned long start_ip = TRAMPOLINE_START;
        uint32_t rel32;
        int i;

        pr_info("allowing %d CPU%s\n", nr_logical_cpuids, (nr_logical_cpuids == 1) ? "" : "s" );

        /* copy trampoline code */
        memcpy(__va(start_ip), _binary_trampoline_start, _binary_trampoline_size);

        /* the last instruction must be jmp rel32 */
        BUG_ON(*(uint8_t *)__va(start_ip + _binary_trampoline_size - 5) != 0xe9);
        /* fill in the address to VMM_START */
        rel32 = addr - (start_ip + _binary_trampoline_size);
        memcpy(__va(start_ip + _binary_trampoline_size - 4), &rel32, sizeof(rel32));

        for (i = 1; i < nr_logical_cpuids; ++i)
                cpu_up(i, start_ip);
}

/*
 * The Multiprocessor Specification 1.4 (1997) example code suggests
 * that there should be a 10ms delay between the BSP asserting INIT
 * and de-asserting INIT, when starting a remote processor.
 * But that slows boot and resume on modern processors, which include
 * many cores and don't require that delay.
 */
unsigned int init_udelay = 0;

static inline void setup_warm_reset_vector(unsigned long start_ip)
{
        rtc_cmos_write(0xa, 0xf);
        *((volatile uint16_t *)__va(TRAMPOLINE_PHYS_HIGH)) = start_ip >> 4;
        *((volatile uint16_t *)__va(TRAMPOLINE_PHYS_LOW)) = start_ip & 0xf;
}

static inline void restore_warm_reset_vector(void)
{
        rtc_cmos_write(0, 0xf);
        *((volatile uint32_t *)__va(TRAMPOLINE_PHYS_LOW)) = 0;
}

static void cpu_up(int cpu, unsigned long start_ip)
{
        extern char __per_cpu_start[], __per_cpu_end[];
        int apicid = cpuid_to_apicid[cpu];
        unsigned long send_status = 0, accept_status = 0;
        int num_starts = 2, j;

        /* set up variables for APs */
        __per_cpu_offset[cpu] = cpu * (__per_cpu_end - __per_cpu_start);
        per_cpu(cpu_number, cpu) = cpu;
        initial_gs = __per_cpu_offset[cpu];
        initial_stack = (uintptr_t)cpu_stacks[cpu] + CPU_STACK_SIZE;

        pr_info("booting cpu %d acpi_id[0x%02x]\n", cpu, apicid);

        atomic_store(&trampoline_status, 0);

        setup_warm_reset_vector(start_ip);

        /* Be paranoid about clearing APIC errors. */
        apic_write(APIC_ESR, 0);
        apic_read(APIC_ESR);

        /* Turn INIT on target chip */
        apic_icr_write(APIC_INT_LEVELTRIG | APIC_INT_ASSERT | APIC_DM_INIT, apicid);

        send_status = safe_apic_wait_icr_idle();

        udelay(init_udelay);

        /* Target chip */
        apic_icr_write(APIC_INT_LEVELTRIG | APIC_DM_INIT, apicid);

        send_status = safe_apic_wait_icr_idle();

        mb();

        /* Run STARTUP IPI loop. */
        for (j = 1; j <= num_starts; j++) {
                apic_write(APIC_ESR, 0);
                apic_read(APIC_ESR);

                /* STARTUP IPI */
                apic_icr_write(APIC_DM_STARTUP | (start_ip >> 12), apicid);

                /* Give the other CPU some time to accept the IPI. */
                if (init_udelay == 0)
                        udelay(10);
                else
                        udelay(300);

                send_status = safe_apic_wait_icr_idle();

                /* Give the other CPU some time to accept the IPI. */
                if (init_udelay == 0)
                        udelay(10);
                else
                        udelay(200);

                apic_write(APIC_ESR, 0);
                accept_status = (apic_read(APIC_ESR) & 0xEF);
                if (send_status || accept_status)
                        break;
        }

        if (send_status)
                pr_err("APIC never delivered???\n");
        if (accept_status)
                pr_err("APIC delivery error (%lx)\n", accept_status);

        if (send_status || accept_status)
                die();

        restore_warm_reset_vector();

        while (atomic_load(&trampoline_status) != TRAMPOLINE_STATUS_STARTED)
                cpu_relax();
}

void smp_notify(void)
{
        atomic_store(&trampoline_status, TRAMPOLINE_STATUS_STARTED);
}

int smp_find_cpu(int apicid)
{
        int i;

        for (i = 0; i < nr_logical_cpuids; ++i) {
                if (cpuid_to_apicid[i] == apicid)
                        return i;
        }
        return -1;
}
