#pragma once

/* Constants used in searching for the RSDP in low memory */

#define ACPI_EBDA_PTR_LOCATION          0x0000040E      /* Physical Address */
#define ACPI_EBDA_PTR_LENGTH            2
#define ACPI_EBDA_WINDOW_SIZE           1024
#define ACPI_HI_RSDP_WINDOW_BASE        0x000E0000      /* Physical Address */
#define ACPI_HI_RSDP_WINDOW_SIZE        0x00020000
#define ACPI_RSDP_SCAN_STEP             16

/* RSDP checksums */

#define ACPI_RSDP_CHECKSUM_LENGTH       20
#define ACPI_RSDP_XCHECKSUM_LENGTH      36
