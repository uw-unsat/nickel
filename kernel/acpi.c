#define pr_fmt(fmt) "acpi: " fmt

#include <sys/errno.h>
#include "acpica/actables.h"

#define ACPI_MAX_TABLES         128

static struct acpi_table_header *initial_tables[ACPI_MAX_TABLES];

void acpi_table_init(void)
{
        acpi_status status;
        acpi_physical_address rsdp_address;

        /* Root Table Array has been statically allocated by the host */
        memset(initial_tables, 0, sizeof(initial_tables));

        /* Get the address of the RSDP */
        status = acpi_find_root_pointer(&rsdp_address);
        if (ACPI_FAILURE(status))
                panic("A valid RSDP was not found\n");

        /*
         * Get the root table (RSDT or XSDT) and extract all entries to the local
         * Root Table Array. This array contains the information of the RSDT/XSDT
         * in a common, more useable format.
         */
        status = acpi_tb_parse_root_table(rsdp_address);
        if (ACPI_FAILURE(status))
                panic("Parsing RSDP failed");
}

/*******************************************************************************
 *
 * FUNCTION:    acpi_tb_get_root_table_entry
 *
 * PARAMETERS:  table_entry         - Pointer to the RSDT/XSDT table entry
 *              table_entry_size    - sizeof 32 or 64 (RSDT or XSDT)
 *
 * RETURN:      Physical address extracted from the root table
 *
 * DESCRIPTION: Get one root table entry. Handles 32-bit and 64-bit cases on
 *              both 32-bit and 64-bit platforms
 *
 * NOTE:        acpi_physical_address is 32-bit on 32-bit platforms, 64-bit on
 *              64-bit platforms.
 *
 ******************************************************************************/

static acpi_physical_address
acpi_tb_get_root_table_entry(uint8_t *table_entry, uint32_t table_entry_size)
{
        /*
         * Get the table physical address (32-bit for RSDT, 64-bit for XSDT):
         * Note: Addresses are 32-bit aligned (not 64) in both RSDT and XSDT
         */
        if (table_entry_size == ACPI_RSDT_ENTRY_SIZE) {
                /*
                 * 32-bit platform, RSDT: Return 32-bit table entry
                 * 64-bit platform, RSDT: Expand 32-bit to 64-bit and return
                 */
                return *(uint32_t *)table_entry;
        } else {
                /*
                 * 32-bit platform, XSDT: Truncate 64-bit to 32-bit and return
                 * 64-bit platform, XSDT: Move (unaligned) 64-bit to local,
                 * return 64-bit
                 */
                return *(uint64_t *)table_entry;
        }
}

/*******************************************************************************
 *
 * FUNCTION:    acpi_tb_parse_root_table
 *
 * PARAMETERS:  rsdp                    - Pointer to the RSDP
 *
 * RETURN:      Status
 *
 * DESCRIPTION: This function is called to parse the Root System Description
 *              Table (RSDT or XSDT)
 *
 * NOTE:        Tables are mapped (not copied) for efficiency. The FACS must
 *              be mapped and cannot be copied because it contains the actual
 *              memory location of the ACPI Global Lock.
 *
 ******************************************************************************/

acpi_status acpi_tb_parse_root_table(acpi_physical_address rsdp_address)
{
        struct acpi_table_rsdp *rsdp;
        uint32_t table_entry_size;
        uint32_t i;
        uint32_t table_count;
        struct acpi_table_header *table;
        acpi_physical_address address;
        uint32_t length;
        uint8_t *table_entry;
        acpi_status status;
        uint32_t table_index;

        /* Map the entire RSDP and extract the address of the RSDT or XSDT */
        rsdp = __va(rsdp_address);
        acpi_tb_print_table_header(rsdp_address, (struct acpi_table_header *)rsdp);

        /* Use XSDT if present and not overridden. Otherwise, use RSDT */
        if ((rsdp->revision > 1) && rsdp->xsdt_physical_address) {
                /*
                 * RSDP contains an XSDT (64-bit physical addresses). We must use
                 * the XSDT if the revision is > 1 and the XSDT pointer is present,
                 * as per the ACPI specification.
                 */
                address = (acpi_physical_address)rsdp->xsdt_physical_address;
                table_entry_size = ACPI_XSDT_ENTRY_SIZE;
        } else {
                /* Root table is an RSDT (32-bit physical addresses) */
                address = (acpi_physical_address)rsdp->rsdt_physical_address;
                table_entry_size = ACPI_RSDT_ENTRY_SIZE;
        }

        /* Map the RSDT/XSDT table header to get the full table length */
        table = __va(address);
        acpi_tb_print_table_header(address, table);

        /*
         * Validate length of the table, and map entire table.
         * Minimum length table must contain at least one entry.
         */
        length = table->length;
        if (length < (sizeof(struct acpi_table_header) + table_entry_size)) {
                pr_err("acpi: invalid table length 0x%X in RSDT/XSDT", length);
                return AE_INVALID_TABLE_LENGTH;
        }

        /* Validate the root table checksum */
        status = acpi_tb_verify_checksum(table, length);
        if (ACPI_FAILURE(status))
                return status;

        /* Get the number of entries and pointer to first entry */
        table_count = (table->length - sizeof(struct acpi_table_header)) / table_entry_size;
        table_entry = (uint8_t *)table + sizeof(struct acpi_table_header);
        table_index = 0;

        /* Initialize the root table array from the RSDT/XSDT */
        for (i = 0; i < table_count; i++) {
                struct acpi_table_header *subtable;
                /* Get the table physical address (32-bit for RSDT, 64-bit for XSDT) */
                address = acpi_tb_get_root_table_entry(table_entry, table_entry_size);

                /* Skip NULL entries in RSDT/XSDT */
                if (!address)
                        goto next_table;

                subtable = __va(address);
                status = acpi_tb_verify_checksum(subtable, subtable->length);
                if (ACPI_FAILURE(status))
                        goto next_table;

                initial_tables[table_index] = subtable;
                acpi_tb_print_table_header(address, subtable);

                table_index++;
                if (table_index == ACPI_MAX_TABLES)
                        break;

next_table:
                table_entry += table_entry_size;
        }

        return AE_OK;
}

static struct acpi_table_header *acpi_find_table(const char *id)
{
        size_t i;
        struct acpi_table_header *table_header;

        for (i = 0; i < ARRAY_SIZE(initial_tables); ++i) {
                table_header = initial_tables[i];
                if (ACPI_COMPARE_NAME(table_header->signature, id))
                        return table_header;
        }
        return NULL;
}

int acpi_table_parse(char *id, acpi_tbl_table_handler handler)
{
        struct acpi_table_header *table;

        table = acpi_find_table(id);
        if (!table)
                return -ENODEV;
        handler(table);
        return 0;
}

int acpi_table_parse_entries_array(char *id,
                        unsigned long table_size,
                        struct acpi_subtable_proc *proc, int proc_num,
                        unsigned int max_entries)
{
        struct acpi_table_header *table_header;
        struct acpi_subtable_header *entry;
        unsigned long table_end;
        int count = 0;
        int i;

        table_header = acpi_find_table(id);
        if (!table_header)
                return -ENODEV;

        table_end = (unsigned long)table_header + table_header->length;

        /* Parse all entries looking for a match. */

        entry = (struct acpi_subtable_header *)((unsigned long)table_header + table_size);

        while (((unsigned long)entry) + sizeof(struct acpi_subtable_header) < table_end) {
                if (max_entries && count >= max_entries)
                        break;

                for (i = 0; i < proc_num; i++) {
                        if (entry->type != proc[i].id)
                                continue;
                        if (proc[i].handler(entry, table_end))
                                panic("acpi: parsing error\n");
                        proc[i].count++;
                        break;
                }

                if (i != proc_num)
                        count++;

                BUG_ON(!entry->length);
                entry = (struct acpi_subtable_header *)((unsigned long)entry + entry->length);
        }

        return count;
}

void acpi_table_print_madt_entry(struct acpi_subtable_header *header)
{
        char *mps_inti_flags_polarity[] = { "dfl", "high", "res", "low" };
        char *mps_inti_flags_trigger[] = { "dfl", "edge", "res", "level" };

        switch (header->type) {

        case ACPI_MADT_TYPE_LOCAL_APIC:
                {
                        struct acpi_madt_local_apic *p =
                            (struct acpi_madt_local_apic *)header;
                        pr_info("LAPIC (acpi_id[0x%02x] lapic_id[0x%02x] %s)\n",
                                p->processor_id, p->id,
                                (p->lapic_flags & ACPI_MADT_ENABLED) ? "enabled" : "disabled");
                }
                break;

        case ACPI_MADT_TYPE_LOCAL_X2APIC:
                {
                        struct acpi_madt_local_x2apic *p =
                            (struct acpi_madt_local_x2apic *)header;
                        pr_info("X2APIC (apic_id[0x%02x] uid[0x%02x] %s)\n",
                                p->local_apic_id, p->uid,
                                (p->lapic_flags & ACPI_MADT_ENABLED) ? "enabled" : "disabled");
                }
                break;

        case ACPI_MADT_TYPE_IO_APIC:
                {
                        struct acpi_madt_io_apic *p =
                            (struct acpi_madt_io_apic *)header;
                        pr_info("IOAPIC (id[0x%02x] address[0x%08x] gsi_base[%d])\n",
                                p->id, p->address, p->global_irq_base);
                }
                break;

        case ACPI_MADT_TYPE_INTERRUPT_OVERRIDE:
                {
                        struct acpi_madt_interrupt_override *p =
                            (struct acpi_madt_interrupt_override *)header;
                        pr_info("INT_SRC_OVR (bus %d bus_irq %d global_irq %d %s %s)\n",
                                p->bus, p->source_irq, p->global_irq,
                                mps_inti_flags_polarity[p->inti_flags & ACPI_MADT_POLARITY_MASK],
                                mps_inti_flags_trigger[(p->inti_flags & ACPI_MADT_TRIGGER_MASK) >> 2]);
                        if (p->inti_flags  &
                            ~(ACPI_MADT_POLARITY_MASK | ACPI_MADT_TRIGGER_MASK))
                                pr_info("INT_SRC_OVR unexpected reserved flags: 0x%x\n",
                                        p->inti_flags  &
                                        ~(ACPI_MADT_POLARITY_MASK | ACPI_MADT_TRIGGER_MASK));
                }
                break;

        case ACPI_MADT_TYPE_NMI_SOURCE:
                {
                        struct acpi_madt_nmi_source *p =
                            (struct acpi_madt_nmi_source *)header;
                        pr_info("NMI_SRC (%s %s global_irq %d)\n",
                                mps_inti_flags_polarity[p->inti_flags & ACPI_MADT_POLARITY_MASK],
                                mps_inti_flags_trigger[(p->inti_flags & ACPI_MADT_TRIGGER_MASK) >> 2],
                                p->global_irq);
                }
                break;

        case ACPI_MADT_TYPE_LOCAL_APIC_NMI:
                {
                        struct acpi_madt_local_apic_nmi *p =
                            (struct acpi_madt_local_apic_nmi *)header;
                        pr_info("LAPIC_NMI (acpi_id[0x%02x] %s %s lint[0x%x])\n",
                                p->processor_id,
                                mps_inti_flags_polarity[p->inti_flags & ACPI_MADT_POLARITY_MASK ],
                                mps_inti_flags_trigger[(p->inti_flags & ACPI_MADT_TRIGGER_MASK) >> 2],
                                p->lint);
                }
                break;

        case ACPI_MADT_TYPE_LOCAL_X2APIC_NMI:
                {
                        uint16_t polarity, trigger;
                        struct acpi_madt_local_x2apic_nmi *p =
                            (struct acpi_madt_local_x2apic_nmi *)header;

                        polarity = p->inti_flags & ACPI_MADT_POLARITY_MASK;
                        trigger = (p->inti_flags & ACPI_MADT_TRIGGER_MASK) >> 2;

                        pr_info("X2APIC_NMI (uid[0x%02x] %s %s lint[0x%x])\n",
                                p->uid,
                                mps_inti_flags_polarity[polarity],
                                mps_inti_flags_trigger[trigger],
                                p->lint);
                }
                break;

        case ACPI_MADT_TYPE_LOCAL_APIC_OVERRIDE:
                {
                        struct acpi_madt_local_apic_override *p =
                            (struct acpi_madt_local_apic_override *)header;
                        pr_info("LAPIC_ADDR_OVR (address[%p])\n",
                                (void *)(unsigned long)p->address);
                }
                break;

        case ACPI_MADT_TYPE_IO_SAPIC:
                {
                        struct acpi_madt_io_sapic *p =
                            (struct acpi_madt_io_sapic *)header;
                        pr_info("IOSAPIC (id[0x%x] address[%p] gsi_base[%d])\n",
                                p->id, (void *)(unsigned long)p->address,
                                p->global_irq_base);
                }
                break;

        case ACPI_MADT_TYPE_LOCAL_SAPIC:
                {
                        struct acpi_madt_local_sapic *p =
                            (struct acpi_madt_local_sapic *)header;
                        pr_info("LSAPIC (acpi_id[0x%02x] lsapic_id[0x%02x] lsapic_eid[0x%02x] %s)\n",
                                p->processor_id, p->id, p->eid,
                                (p->lapic_flags & ACPI_MADT_ENABLED) ? "enabled" : "disabled");
                }
                break;

        case ACPI_MADT_TYPE_INTERRUPT_SOURCE:
                {
                        struct acpi_madt_interrupt_source *p =
                            (struct acpi_madt_interrupt_source *)header;
                        pr_info("PLAT_INT_SRC (%s %s type[0x%x] id[0x%04x] eid[0x%x] iosapic_vector[0x%x] global_irq[0x%x]\n",
                                mps_inti_flags_polarity[p->inti_flags & ACPI_MADT_POLARITY_MASK],
                                mps_inti_flags_trigger[(p->inti_flags & ACPI_MADT_TRIGGER_MASK) >> 2],
                                p->type, p->id, p->eid, p->io_sapic_vector,
                                p->global_irq);
                }
                break;

        case ACPI_MADT_TYPE_GENERIC_INTERRUPT:
                {
                        struct acpi_madt_generic_interrupt *p =
                                (struct acpi_madt_generic_interrupt *)header;
                        pr_info("GICC (acpi_id[0x%04x] address[%" PRIx64 "] MPIDR[0x%" PRIx64 "] %s)\n",
                                p->uid, p->base_address,
                                p->arm_mpidr,
                                (p->flags & ACPI_MADT_ENABLED) ? "enabled" : "disabled");

                }
                break;

        case ACPI_MADT_TYPE_GENERIC_DISTRIBUTOR:
                {
                        struct acpi_madt_generic_distributor *p =
                                (struct acpi_madt_generic_distributor *)header;
                        pr_info("GIC Distributor (gic_id[0x%04x] address[%" PRIx64 "] gsi_base[%d])\n",
                                p->gic_id, p->base_address,
                                p->global_irq_base);
                }
                break;

        default:
                pr_warn("Found unsupported MADT entry (type = 0x%x)\n",
                        header->type);
                break;
        }
}
