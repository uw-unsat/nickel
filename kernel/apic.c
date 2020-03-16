#define pr_fmt(fmt) __MODULE__ ": " fmt

#include <asm/apic.h>
#include <asm/cpufeature.h>
#include <asm/irq.h>
#include <asm/msr.h>
#include <asm/smp.h>
#include <sys/acpi.h>

#define BAD_MADT_ENTRY(entry, end) (                                        \
                (!entry) || (unsigned long)entry + sizeof(*entry) > end ||  \
                ((struct acpi_subtable_header *)entry)->length < sizeof(*entry))

/* Clock divisor */
#define APIC_DIVISOR    16

struct apic *apic;

/*
 * The number of allocated logical CPU IDs. Since logical CPU IDs are allocated
 * contiguously, it equals to current allocated max logical CPU ID plus 1.
 * All allocated CPU IDs should be in the [0, nr_logical_cpuids) range,
 * so the maximum of nr_logical_cpuids is nr_cpu_ids.
 *
 * NOTE: Reserve 0 for BSP.
 */
int nr_logical_cpuids = 1;

/* Used to store mapping between logical CPU IDs and APIC IDs. */
int cpuid_to_apicid[] = {
        [0 ... NR_CPUS - 1] = BAD_APICID,
};

static unsigned int boot_cpu_physical_apicid = BAD_APICID;

static int acpi_parse_madt(struct acpi_table_header *table)
{
        struct acpi_table_madt *madt;

        madt = (struct acpi_table_madt *)table;
        acpi_lapic_addr = madt->address;
        return 0;
}

static void acpi_register_lapic(int apicid, uint8_t enabled)
{
        int i;

        if (!enabled)
                panic("no CPU hotplug support\n");

        if (apicid == boot_cpu_physical_apicid) {
                /* Logical cpuid 0 is reserved for BSP. */
                cpuid_to_apicid[0] = apicid;
                return;
        }

        /* Check if the apicid exists. */
        for (i = 0; i < nr_logical_cpuids; i++) {
                if (cpuid_to_apicid[i] == apicid)
                        return;
        }

        /* Allocate a new cpuid.  Warn if we run out of cpu ids. */
        if (nr_logical_cpuids >= NR_CPUS) {
                pr_warn("NR_CPUS limit of %i reached\n", nr_logical_cpuids);
                return;
        }

        cpuid_to_apicid[nr_logical_cpuids] = apicid;
        nr_logical_cpuids++;
}

static int acpi_parse_lapic(struct acpi_subtable_header *header, const unsigned long end)
{
        struct acpi_madt_local_apic *processor;
        int apicid;
        uint8_t enabled;

        processor = (struct acpi_madt_local_apic *)header;
        BUG_ON(BAD_MADT_ENTRY(processor, end));

        acpi_table_print_madt_entry(header);

        apicid = processor->id;
        enabled = processor->lapic_flags & ACPI_MADT_ENABLED;
        acpi_register_lapic(apicid, enabled);
        return 0;
}

static int acpi_parse_x2apic(struct acpi_subtable_header *header, const unsigned long end)
{
        struct acpi_madt_local_x2apic *processor;
        int apicid;
        uint8_t enabled;

        processor = (struct acpi_madt_local_x2apic *)header;
        BUG_ON(BAD_MADT_ENTRY(processor, end));

        acpi_table_print_madt_entry(header);

        apicid = processor->local_apic_id;
        enabled = processor->lapic_flags & ACPI_MADT_ENABLED;
        acpi_register_lapic(apicid, enabled);
        return 0;
}

static int acpi_parse_madt_lapic_entries(void)
{
        struct acpi_subtable_proc madt_proc[] = {
                { .id = ACPI_MADT_TYPE_LOCAL_APIC,
                  .handler = acpi_parse_lapic,
                },
                { .id = ACPI_MADT_TYPE_LOCAL_X2APIC,
                  .handler = acpi_parse_x2apic,
                },
        };

        return acpi_table_parse_entries_array(
                ACPI_SIG_MADT, sizeof(struct acpi_table_madt),
                madt_proc, ARRAY_SIZE(madt_proc), MAX_LOCAL_APIC);
}

static void x2apic_enable(void)
{
        uint64_t msr;

        msr = rdmsrl(MSR_IA32_APICBASE);
        if (msr & MSR_IA32_APICBASE_X2APIC_ENABLE)
                return;
        wrmsrl(MSR_IA32_APICBASE, msr | MSR_IA32_APICBASE_X2APIC_ENABLE);
}

static void verify_apic(void)
{
        uint64_t msr;

        BUG_ON(!this_cpu_has(X86_FEATURE_APIC));
        msr = rdmsrl(MSR_IA32_APICBASE);

        if (!(msr & MSR_IA32_APICBASE_ENABLE))
                panic("xapic disabled\n");

        /* BSP */
        if (!apic) {
                /* check if BIOS has enabled x2apic */
                if (msr & MSR_IA32_APICBASE_X2APIC_ENABLE)
                        apic = &x2apic;
                else
                        apic = &xapic;
                return;
        }

        /* AP: let's turn on x2apic if BSP has done so */
        if (apic == &x2apic) {
                BUG_ON(!this_cpu_has(X86_FEATURE_X2APIC));
                x2apic_enable();
        }
}

/**
 * clear_local_apic - shutdown the local APIC
 *
 * This is called, when a CPU is disabled and before rebooting, so the state of
 * the local APIC has no dangling leftovers. Also used to cleanout any BIOS
 * leftovers during boot.
 */
static void clear_local_apic(void)
{
        uint32_t v;

        /*
         * Masking an LVT entry can trigger a local APIC error
         * if the vector is zero. Mask LVTERR first to prevent this.
         */
        v = ERROR_APIC_VECTOR; /* any non-zero vector will do */
        apic_write(APIC_LVTERR, v | APIC_LVT_MASKED);

        /*
         * Careful: we have to set masks only first to deassert
         * any level-triggered sources.
         */
        v = apic_read(APIC_LVTT);
        apic_write(APIC_LVTT, v | APIC_LVT_MASKED);
        v = apic_read(APIC_LVT0);
        apic_write(APIC_LVT0, v | APIC_LVT_MASKED);
        v = apic_read(APIC_LVT1);
        apic_write(APIC_LVT1, v | APIC_LVT_MASKED);
        v = apic_read(APIC_LVTPC);
        apic_write(APIC_LVTPC, v | APIC_LVT_MASKED);

        /* Clean APIC state */
        apic_write(APIC_LVTT, APIC_LVT_MASKED);
        apic_write(APIC_LVT0, APIC_LVT_MASKED);
        apic_write(APIC_LVT1, APIC_LVT_MASKED);
        apic_write(APIC_LVTERR, APIC_LVT_MASKED);
        apic_write(APIC_LVTPC, APIC_LVT_MASKED);

        apic_write(APIC_ESR, 0);
        apic_read(APIC_ESR);
}

static void lapic_setup_esr(void)
{
        unsigned int oldvalue, value;

        apic_write(APIC_ESR, 0);
        oldvalue = apic_read(APIC_ESR);

        /* enables sending errors */
        value = ERROR_APIC_VECTOR;
        apic_write(APIC_LVTERR, value);

        /* spec says clear errors after enabling vector */
        apic_write(APIC_ESR, 0);
        value = apic_read(APIC_ESR);

        if (value != oldvalue)
                pr_info("ESR value before enabling vector: 0x%08x  after: 0x%08x\n",
                        oldvalue, value);
}

static void setup_local_apic(void)
{
        unsigned int value;

        /* Intel recommends to set DFR, LDR and TPR before enabling an APIC. */
        apic->init_apic_ldr();

        /* Set Task Priority to 'accept all'. We never change this later on. */
        value = apic_read(APIC_TASKPRI);
        value &= ~APIC_TPRI_MASK;
        apic_write(APIC_TASKPRI, value);

        /* Now that we are all set up, enable the APIC. */
        value = apic_read(APIC_SPIV);
        value &= ~APIC_VECTOR_MASK;
        value |= APIC_SPIV_APIC_ENABLED;

        /* Set spurious IRQ vector. */
        value |= SPURIOUS_APIC_VECTOR;
        apic_write(APIC_SPIV, value);
}

void apic_init(void)
{
        /* choose xapic/x2apic based on BIOS setup */
        verify_apic();

        /* BSP */
        if (boot_cpu_physical_apicid == BAD_APICID) {
                int r;

                /* run acpi_table_parse first to initialize acpi_lapic_addr for apic ops */
                r = acpi_table_parse(ACPI_SIG_MADT, acpi_parse_madt);
                BUG_ON(r);

                /* initialize boot_cpu_physical_apicid before parsing madt entries */
                boot_cpu_physical_apicid = read_apic_id();
                r = acpi_parse_madt_lapic_entries();
                BUG_ON(r < 0);

                if (cpuid_to_apicid[0] != boot_cpu_physical_apicid)
                        panic("BIOS bug: boot cpu not detected!\n");

        }

        /* do not trust the local APIC being empty at bootup */
        clear_local_apic();

        /* enable BSP APIC */
        setup_local_apic();

        lapic_setup_esr();
}

void x2apic_init(void)
{
        /* must be called from BSP */
        BUG_ON(smp_processor_id() != 0);
        BUG_ON(apic != &xapic);

        if (!this_cpu_has(X86_FEATURE_X2APIC))
                return;

        x2apic_enable();
        apic = &x2apic;
        pr_info("x2apic enabled\n");
}

void lapic_timer_set_periodic(uint32_t clocks)
{
        uint32_t lvtt_value, tmp_value;

        lvtt_value = LOCAL_TIMER_VECTOR | APIC_LVT_TIMER_PERIODIC;
        apic_write(APIC_LVTT, lvtt_value);

        /* Divide PICLK by 16 */
        tmp_value = apic_read(APIC_TDCR);
        apic_write(APIC_TDCR,
                (tmp_value & ~(APIC_TDR_DIV_1 | APIC_TDR_DIV_TMBASE)) |
                APIC_TDR_DIV_16);

        apic_write(APIC_TMICT, clocks / APIC_DIVISOR);
}
