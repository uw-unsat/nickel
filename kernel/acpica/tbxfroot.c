#include "actables.h"

/*******************************************************************************
 *
 * FUNCTION:    acpi_tb_validate_rsdp
 *
 * PARAMETERS:  rsdp                - Pointer to unvalidated RSDP
 *
 * RETURN:      Status
 *
 * DESCRIPTION: Validate the RSDP (ptr)
 *
 ******************************************************************************/

acpi_status acpi_tb_validate_rsdp(struct acpi_table_rsdp *rsdp)
{
        /*
         * The signature and checksum must both be correct
         *
         * Note: Sometimes there exists more than one RSDP in memory; the valid
         * RSDP has a valid checksum, all others have an invalid checksum.
         */
        if (!ACPI_VALIDATE_RSDP_SIG(rsdp->signature)) {
                /* Nope, BAD Signature */
                return AE_BAD_SIGNATURE;
        }

        /* Check the standard checksum */
        if (acpi_tb_checksum((uint8_t *) rsdp, ACPI_RSDP_CHECKSUM_LENGTH) != 0)
                return AE_BAD_CHECKSUM;

        /* Check extended checksum if table version >= 2 */

        if ((rsdp->revision >= 2) &&
            (acpi_tb_checksum((uint8_t *) rsdp, ACPI_RSDP_XCHECKSUM_LENGTH) != 0)) {
                return AE_BAD_CHECKSUM;
        }

        return AE_OK;
}


/*******************************************************************************
 *
 * FUNCTION:    acpi_find_root_pointer
 *
 * PARAMETERS:  table_address           - Where the table pointer is returned
 *
 * RETURN:      Status, RSDP physical address
 *
 * DESCRIPTION: Search lower 1Mbyte of memory for the root system descriptor
 *              pointer structure. If it is found, set *RSDP to point to it.
 *
 * NOTE1:       The RSDP must be either in the first 1K of the Extended
 *              BIOS Data Area or between E0000 and FFFFF (From ACPI Spec.)
 *              Only a 32-bit physical address is necessary.
 *
 * NOTE2:       This function is always available, regardless of the
 *              initialization state of the rest of ACPI.
 *
 ******************************************************************************/
acpi_status acpi_find_root_pointer(acpi_physical_address *table_address)
{
        uint8_t *table_ptr;
        uint8_t *mem_rover;
        uint32_t physical_address;

        /* 1a) Get the location of the Extended BIOS Data Area (EBDA) */
        physical_address = ACPI_EBDA_PTR_LOCATION;

        /* Convert segment part to physical address */
        physical_address <<= 4;

        /* EBDA present? */
        if (physical_address > 0x400) {
                /*
                 * 1b) Search EBDA paragraphs (EBDA is required to be a
                 *     minimum of 1K length)
                 */
                table_ptr = __va(physical_address);
                mem_rover = acpi_tb_scan_memory_for_rsdp(table_ptr, ACPI_EBDA_WINDOW_SIZE);

                if (mem_rover) {
                        /* Return the physical address */
                        physical_address += (uint32_t)ACPI_PTR_DIFF(mem_rover, table_ptr);
                        *table_address =(acpi_physical_address)physical_address;
                        return AE_OK;
                }
        }

        /*
         * 2) Search upper memory: 16-byte boundaries in E0000h-FFFFFh
         */
        table_ptr = __va(ACPI_HI_RSDP_WINDOW_BASE);
        mem_rover = acpi_tb_scan_memory_for_rsdp(table_ptr, ACPI_HI_RSDP_WINDOW_SIZE);

        if (mem_rover) {
                /* Return the physical address */
                *table_address = ACPI_HI_RSDP_WINDOW_BASE + ACPI_PTR_DIFF(mem_rover, table_ptr);
                return AE_OK;
        }

        /* A valid RSDP was not found */
        return AE_NOT_FOUND;
}

/*******************************************************************************
 *
 * FUNCTION:    acpi_tb_scan_memory_for_rsdp
 *
 * PARAMETERS:  start_address       - Starting pointer for search
 *              length              - Maximum length to search
 *
 * RETURN:      Pointer to the RSDP if found, otherwise NULL.
 *
 * DESCRIPTION: Search a block of memory for the RSDP signature
 *
 ******************************************************************************/
uint8_t *acpi_tb_scan_memory_for_rsdp(uint8_t *start_address, uint32_t length)
{
        acpi_status status;
        uint8_t *mem_rover;
        uint8_t *end_address;

        end_address = start_address + length;

        /* Search from given start address for the requested length */
        for (mem_rover = start_address; mem_rover < end_address;
             mem_rover += ACPI_RSDP_SCAN_STEP) {
                /* The RSDP signature and checksum must both be correct */
                status = acpi_tb_validate_rsdp((struct acpi_table_rsdp *)mem_rover);
                if (ACPI_SUCCESS(status))
                        return mem_rover;
                /* No sig match or bad checksum, keep searching */
        }

        /* Searched entire block, no RSDP was found */
        return NULL;
}
