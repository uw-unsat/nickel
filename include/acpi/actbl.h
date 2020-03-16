#pragma once

#include <acpi/actypes.h>

/*
 * Values for description table header signatures for tables defined in this
 * file. Useful because they make it more difficult to inadvertently type in
 * the wrong signature.
 */
#define ACPI_SIG_DSDT           "DSDT"  /* Differentiated System Description Table */
#define ACPI_SIG_FADT           "FACP"  /* Fixed ACPI Description Table */
#define ACPI_SIG_FACS           "FACS"  /* Firmware ACPI Control Structure */
#define ACPI_SIG_OSDT           "OSDT"  /* Override System Description Table */
#define ACPI_SIG_PSDT           "PSDT"  /* Persistent System Description Table */
#define ACPI_SIG_RSDP           "RSD PTR "      /* Root System Description Pointer */
#define ACPI_SIG_RSDT           "RSDT"  /* Root System Description Table */
#define ACPI_SIG_XSDT           "XSDT"  /* Extended  System Description Table */
#define ACPI_SIG_SSDT           "SSDT"  /* Secondary System Description Table */
#define ACPI_RSDP_NAME          "RSDP"  /* Short name for RSDP, not signature */

/*
 * All tables and structures must be byte-packed to match the ACPI
 * specification, since the tables are provided by the system BIOS
 */
#pragma pack(1)

/*
 * Note: C bitfields are not used for this reason:
 *
 * "Bitfields are great and easy to read, but unfortunately the C language
 * does not specify the layout of bitfields in memory, which means they are
 * essentially useless for dealing with packed data in on-disk formats or
 * binary wire protocols." (Or ACPI tables and buffers.) "If you ask me,
 * this decision was a design error in C. Ritchie could have picked an order
 * and stuck with it." Norman Ramsey.
 * See http://stackoverflow.com/a/1053662/41661
 */

/*******************************************************************************
 *
 * Master ACPI Table Header. This common header is used by all ACPI tables
 * except the RSDP and FACS.
 *
 ******************************************************************************/

struct acpi_table_header {
        char signature[ACPI_NAME_SIZE]; /* ASCII table signature */
        uint32_t length;                /* Length of table in bytes, including this header */
        uint8_t revision;               /* ACPI Specification minor version number */
        uint8_t checksum;               /* To make sum of entire table == 0 */
        char oem_id[ACPI_OEM_ID_SIZE];  /* ASCII OEM identification */
        char oem_table_id[ACPI_OEM_TABLE_ID_SIZE];      /* ASCII OEM table identification */
        uint32_t oem_revision;  /* OEM revision number */
        char asl_compiler_id[ACPI_NAME_SIZE];   /* ASCII ASL compiler vendor ID */
        uint32_t asl_compiler_revision; /* ASL compiler version */
};

/*******************************************************************************
 *
 * GAS - Generic Address Structure (ACPI 2.0+)
 *
 * Note: Since this structure is used in the ACPI tables, it is byte aligned.
 * If misaligned access is not supported by the hardware, accesses to the
 * 64-bit Address field must be performed with care.
 *
 ******************************************************************************/

struct acpi_generic_address {
        uint8_t space_id;       /* Address space where struct or register exists */
        uint8_t bit_width;      /* Size in bits of given register */
        uint8_t bit_offset;     /* Bit offset within the register */
        uint8_t access_width;   /* Minimum Access size (ACPI 3.0) */
        uint64_t address;       /* 64-bit address of struct or register */
};

/*******************************************************************************
 *
 * RSDP - Root System Description Pointer (Signature is "RSD PTR ")
 *        Version 2
 *
 ******************************************************************************/

struct acpi_table_rsdp {
        char signature[8];              /* ACPI signature, contains "RSD PTR " */
        uint8_t checksum;               /* ACPI 1.0 checksum */
        char oem_id[ACPI_OEM_ID_SIZE];  /* OEM identification */
        uint8_t revision;               /* Must be (0) for ACPI 1.0 or (2) for ACPI 2.0+ */
        uint32_t rsdt_physical_address; /* 32-bit physical address of the RSDT */
        uint32_t length;                /* Table length in bytes, including header (ACPI 2.0+) */
        uint64_t xsdt_physical_address; /* 64-bit physical address of the XSDT (ACPI 2.0+) */
        uint8_t extended_checksum;      /* Checksum of entire table (ACPI 2.0+) */
        uint8_t reserved[3];            /* Reserved, must be zero */
};

/* Standalone struct for the ACPI 1.0 RSDP */

struct acpi_rsdp_common {
        char signature[8];
        uint8_t checksum;
        char oem_id[ACPI_OEM_ID_SIZE];
        uint8_t revision;
        uint32_t rsdt_physical_address;
};

/* Standalone struct for the extended part of the RSDP (ACPI 2.0+) */

struct acpi_rsdp_extension {
        uint32_t length;
        uint64_t xsdt_physical_address;
        uint8_t extended_checksum;
        uint8_t reserved[3];
};

/*******************************************************************************
 *
 * RSDT/XSDT - Root System Description Tables
 *             Version 1 (both)
 *
 ******************************************************************************/

struct acpi_table_rsdt {
        struct acpi_table_header header;        /* Common ACPI table header */
        uint32_t table_offset_entry[1];         /* Array of pointers to ACPI tables */
};

struct acpi_table_xsdt {
        struct acpi_table_header header;        /* Common ACPI table header */
        uint64_t table_offset_entry[1];         /* Array of pointers to ACPI tables */
};

#define ACPI_RSDT_ENTRY_SIZE        (sizeof(uint32_t))
#define ACPI_XSDT_ENTRY_SIZE        (sizeof(uint64_t))

/* Reset to default packing */

#pragma pack()
