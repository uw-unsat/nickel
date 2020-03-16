#pragma once

/*******************************************************************************
 *
 * Additional ACPI Tables (3)
 *
 * These tables are not consumed directly by the ACPICA subsystem, but are
 * included here to support device drivers and the AML disassembler.
 *
 * In general, the tables in this file are fully defined within the ACPI
 * specification.
 *
 ******************************************************************************/

/*
 * Values for description table header signatures for tables defined in this
 * file. Useful because they make it more difficult to inadvertently type in
 * the wrong signature.
 */
#define ACPI_SIG_BGRT           "BGRT"  /* Boot Graphics Resource Table */
#define ACPI_SIG_DRTM           "DRTM"  /* Dynamic Root of Trust for Measurement table */
#define ACPI_SIG_FPDT           "FPDT"  /* Firmware Performance Data Table */
#define ACPI_SIG_GTDT           "GTDT"  /* Generic Timer Description Table */
#define ACPI_SIG_MPST           "MPST"  /* Memory Power State Table */
#define ACPI_SIG_PCCT           "PCCT"  /* Platform Communications Channel Table */
#define ACPI_SIG_PMTT           "PMTT"  /* Platform Memory Topology Table */
#define ACPI_SIG_RASF           "RASF"  /* RAS Feature table */
#define ACPI_SIG_STAO           "STAO"  /* Status Override table */
#define ACPI_SIG_WPBT           "WPBT"  /* Windows Platform Binary Table */
#define ACPI_SIG_XENV           "XENV"  /* Xen Environment table */

#define ACPI_SIG_S3PT           "S3PT"  /* S3 Performance (sub)Table */
#define ACPI_SIG_PCCS           "PCC"   /* PCC Shared Memory Region */

/* Reserved table signatures */

#define ACPI_SIG_MATR           "MATR"  /* Memory Address Translation Table */
#define ACPI_SIG_MSDM           "MSDM"  /* Microsoft Data Management Table */

