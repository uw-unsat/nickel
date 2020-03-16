#include <sys/ctype.h>
#include "actables.h"

/*******************************************************************************
 *
 * FUNCTION:    acpi_tb_fix_string
 *
 * PARAMETERS:  string              - String to be repaired
 *              length              - Maximum length
 *
 * RETURN:      None
 *
 * DESCRIPTION: Replace every non-printable or non-ascii byte in the string
 *              with a question mark '?'.
 *
 ******************************************************************************/

static void acpi_tb_fix_string(char *string, acpi_size length)
{

        while (length && *string) {
                if (!isprint((int)*string)) {
                        *string = '?';
                }

                string++;
                length--;
        }
}

/*******************************************************************************
 *
 * FUNCTION:    acpi_tb_cleanup_table_header
 *
 * PARAMETERS:  out_header          - Where the cleaned header is returned
 *              header              - Input ACPI table header
 *
 * RETURN:      Returns the cleaned header in out_header
 *
 * DESCRIPTION: Copy the table header and ensure that all "string" fields in
 *              the header consist of printable characters.
 *
 ******************************************************************************/

static void acpi_tb_cleanup_table_header(struct acpi_table_header *out_header,
                                         struct acpi_table_header *header)
{

        memcpy(out_header, header, sizeof(struct acpi_table_header));

        acpi_tb_fix_string(out_header->signature, ACPI_NAME_SIZE);
        acpi_tb_fix_string(out_header->oem_id, ACPI_OEM_ID_SIZE);
        acpi_tb_fix_string(out_header->oem_table_id, ACPI_OEM_TABLE_ID_SIZE);
        acpi_tb_fix_string(out_header->asl_compiler_id, ACPI_NAME_SIZE);
}

/*******************************************************************************
 *
 * FUNCTION:    acpi_tb_print_table_header
 *
 * PARAMETERS:  address             - Table physical address
 *              header              - Table header
 *
 * RETURN:      None
 *
 * DESCRIPTION: Print an ACPI table header. Special cases for FACS and RSDP.
 *
 ******************************************************************************/

void acpi_tb_print_table_header(acpi_physical_address address,
                                struct acpi_table_header *header)
{
        struct acpi_table_header local_header;

        if (ACPI_COMPARE_NAME(header->signature, ACPI_SIG_FACS)) {

                /* FACS only has signature and length fields */

                pr_info("acpi: %-4.4s 0x%8.8x%8.8x %06x\n",
                        header->signature, ACPI_FORMAT_UINT64(address),
                        header->length);
        } else if (ACPI_VALIDATE_RSDP_SIG(header->signature)) {

                /* RSDP has no common fields */

                memcpy(local_header.oem_id,
                       ((struct acpi_table_rsdp *)header)->oem_id,
                       ACPI_OEM_ID_SIZE);
                acpi_tb_fix_string(local_header.oem_id, ACPI_OEM_ID_SIZE);

                pr_info("acpi: RSDP 0x%8.8x%8.8x %06x (v%.2d %-6.6s)\n",
                        ACPI_FORMAT_UINT64(address),
                        (((struct acpi_table_rsdp *)header)->revision > 0)
                        ? ((struct acpi_table_rsdp *)header)->length : 20,
                        ((struct acpi_table_rsdp *)header)->revision,
                        local_header.oem_id);
        } else {
                /* Standard ACPI table with full common header */

                acpi_tb_cleanup_table_header(&local_header, header);

                pr_info("acpi: %-4.4s 0x%8.8x%8.8x"
                        " %06x (v%.2d %-6.6s %-8.8s %08x %-4.4s %08x)\n",
                        local_header.signature, ACPI_FORMAT_UINT64(address),
                        local_header.length, local_header.revision,
                        local_header.oem_id, local_header.oem_table_id,
                        local_header.oem_revision,
                        local_header.asl_compiler_id,
                        local_header.asl_compiler_revision);
        }
}

/*******************************************************************************
 *
 * FUNCTION:    acpi_tb_validate_checksum
 *
 * PARAMETERS:  table               - ACPI table to verify
 *              length              - Length of entire table
 *
 * RETURN:      Status
 *
 * DESCRIPTION: Verifies that the table checksums to zero. Optionally returns
 *              exception on bad checksum.
 *
 ******************************************************************************/

acpi_status acpi_tb_verify_checksum(struct acpi_table_header *table, uint32_t length)
{
        uint8_t checksum;

        /*
         * FACS/S3PT:
         * They are the odd tables, have no standard ACPI header and no checksum
         */
        if (ACPI_COMPARE_NAME(table->signature, ACPI_SIG_S3PT) ||
            ACPI_COMPARE_NAME(table->signature, ACPI_SIG_FACS)) {
                return AE_OK;
        }

        /* Compute the checksum on the table */
        checksum = acpi_tb_checksum((uint8_t *)table, length);

        /* Checksum ok? (should be zero) */
        if (checksum) {
                pr_err("acpi: incorrect checksum in table [%4.4s] - 0x%2.2x, "
                       "should be 0x%2.2x",
                       table->signature, table->checksum,
                       (uint8_t)(table->checksum - checksum));
                return AE_BAD_CHECKSUM;
        }

        return AE_OK;
}

/*******************************************************************************
 *
 * FUNCTION:    acpi_tb_checksum
 *
 * PARAMETERS:  buffer          - Pointer to memory region to be checked
 *              length          - Length of this memory region
 *
 * RETURN:      Checksum u8
 *
 * DESCRIPTION: Calculates circular checksum of memory region.
 *
 ******************************************************************************/

uint8_t acpi_tb_checksum(uint8_t *buffer, uint32_t length)
{
        uint8_t sum = 0;
        uint8_t *end = buffer + length;

        while (buffer < end) {
                sum = (uint8_t)(sum + *buffer);
                ++buffer;
        }

        return sum;
}
