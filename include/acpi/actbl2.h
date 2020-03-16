#pragma once

#include <acpi/actypes.h>

/*******************************************************************************
 *
 * Additional ACPI Tables (2)
 *
 * These tables are not consumed directly by the ACPICA subsystem, but are
 * included here to support device drivers and the AML disassembler.
 *
 * Generally, the tables in this file are defined by third-party specifications,
 * and are not defined directly by the ACPI specification itself.
 *
 ******************************************************************************/

/*
 * Values for description table header signatures for tables defined in this
 * file. Useful because they make it more difficult to inadvertently type in
 * the wrong signature.
 */
#define ACPI_SIG_ASF            "ASF!"  /* Alert Standard Format table */
#define ACPI_SIG_BOOT           "BOOT"  /* Simple Boot Flag Table */
#define ACPI_SIG_CSRT           "CSRT"  /* Core System Resource Table */
#define ACPI_SIG_DBG2           "DBG2"  /* Debug Port table type 2 */
#define ACPI_SIG_DBGP           "DBGP"  /* Debug Port table */
#define ACPI_SIG_DMAR           "DMAR"  /* DMA Remapping table */
#define ACPI_SIG_HPET           "HPET"  /* High Precision Event Timer table */
#define ACPI_SIG_IBFT           "IBFT"  /* iSCSI Boot Firmware Table */
#define ACPI_SIG_IORT           "IORT"  /* IO Remapping Table */
#define ACPI_SIG_IVRS           "IVRS"  /* I/O Virtualization Reporting Structure */
#define ACPI_SIG_LPIT           "LPIT"  /* Low Power Idle Table */
#define ACPI_SIG_MCFG           "MCFG"  /* PCI Memory Mapped Configuration table */
#define ACPI_SIG_MCHI           "MCHI"  /* Management Controller Host Interface table */
#define ACPI_SIG_MSDM           "MSDM"  /* Microsoft Data Management Table */
#define ACPI_SIG_MTMR           "MTMR"  /* MID Timer table */
#define ACPI_SIG_SDEI           "SDEI"  /* Software Delegated Exception Interface Table */
#define ACPI_SIG_SLIC           "SLIC"  /* Software Licensing Description Table */
#define ACPI_SIG_SPCR           "SPCR"  /* Serial Port Console Redirection table */
#define ACPI_SIG_SPMI           "SPMI"  /* Server Platform Management Interface table */
#define ACPI_SIG_TCPA           "TCPA"  /* Trusted Computing Platform Alliance table */
#define ACPI_SIG_TPM2           "TPM2"  /* Trusted Platform Module 2.0 H/W interface table */
#define ACPI_SIG_UEFI           "UEFI"  /* Uefi Boot Optimization Table */
#define ACPI_SIG_VRTC           "VRTC"  /* Virtual Real Time Clock Table */
#define ACPI_SIG_WAET           "WAET"  /* Windows ACPI Emulated devices Table */
#define ACPI_SIG_WDAT           "WDAT"  /* Watchdog Action Table */
#define ACPI_SIG_WDDT           "WDDT"  /* Watchdog Timer Description Table */
#define ACPI_SIG_WDRT           "WDRT"  /* Watchdog Resource Table */
#define ACPI_SIG_WSMT           "WSMT"  /* Windows SMM Security Migrations Table */
#define ACPI_SIG_XXXX           "XXXX"  /* Intermediate AML header for ASL/ASL+ converter */


/*
 * All tables must be byte-packed to match the ACPI specification, since
 * the tables are provided by the system BIOS.
 */
#pragma pack(1)

/*******************************************************************************
 *
 * DMAR - DMA Remapping table
 *        Version 1
 *
 * Conforms to "Intel Virtualization Technology for Directed I/O",
 * Version 2.3, October 2014
 *
 ******************************************************************************/

struct acpi_table_dmar {
        struct acpi_table_header header;        /* Common ACPI table header */
        uint8_t width;               /* Host Address Width */
        uint8_t flags;
        uint8_t reserved[10];
};

/* Masks for Flags field above */

#define ACPI_DMAR_INTR_REMAP        (1)
#define ACPI_DMAR_X2APIC_OPT_OUT    (1<<1)
#define ACPI_DMAR_X2APIC_MODE       (1<<2)

/* DMAR subtable header */

struct acpi_dmar_header {
        uint16_t type;
        uint16_t length;
};

/* Values for subtable type in struct acpi_dmar_header */

enum acpi_dmar_type {
        ACPI_DMAR_TYPE_HARDWARE_UNIT = 0,
        ACPI_DMAR_TYPE_RESERVED_MEMORY = 1,
        ACPI_DMAR_TYPE_ROOT_ATS = 2,
        ACPI_DMAR_TYPE_HARDWARE_AFFINITY = 3,
        ACPI_DMAR_TYPE_NAMESPACE = 4,
        ACPI_DMAR_TYPE_RESERVED = 5     /* 5 and greater are reserved */
};

/* DMAR Device Scope structure */

struct acpi_dmar_device_scope {
        uint8_t entry_type;
        uint8_t length;
        uint16_t reserved;
        uint8_t enumeration_id;
        uint8_t bus;
};

/* Values for entry_type in struct acpi_dmar_device_scope - device types */

enum acpi_dmar_scope_type {
        ACPI_DMAR_SCOPE_TYPE_NOT_USED = 0,
        ACPI_DMAR_SCOPE_TYPE_ENDPOINT = 1,
        ACPI_DMAR_SCOPE_TYPE_BRIDGE = 2,
        ACPI_DMAR_SCOPE_TYPE_IOAPIC = 3,
        ACPI_DMAR_SCOPE_TYPE_HPET = 4,
        ACPI_DMAR_SCOPE_TYPE_NAMESPACE = 5,
        ACPI_DMAR_SCOPE_TYPE_RESERVED = 6       /* 6 and greater are reserved */
};

struct acpi_dmar_pci_path {
        uint8_t device;
        uint8_t function;
};

/*
 * DMAR Subtables, correspond to Type in struct acpi_dmar_header
 */

/* 0: Hardware Unit Definition */

struct acpi_dmar_hardware_unit {
        struct acpi_dmar_header header;
        uint8_t flags;
        uint8_t reserved;
        uint16_t segment;
        uint64_t address;            /* Register Base Address */
};

/* Masks for Flags field above */

#define ACPI_DMAR_INCLUDE_ALL       (1)

/* 1: Reserved Memory Defininition */

struct acpi_dmar_reserved_memory {
        struct acpi_dmar_header header;
        uint16_t reserved;
        uint16_t segment;
        uint64_t base_address;       /* 4K aligned base address */
        uint64_t end_address;        /* 4K aligned limit address */
};

/* Masks for Flags field above */

#define ACPI_DMAR_ALLOW_ALL         (1)

/* 2: Root Port ATS Capability Reporting Structure */

struct acpi_dmar_atsr {
        struct acpi_dmar_header header;
        uint8_t flags;
        uint8_t reserved;
        uint16_t segment;
};

/* Masks for Flags field above */

#define ACPI_DMAR_ALL_PORTS         (1)

/* 3: Remapping Hardware Static Affinity Structure */

struct acpi_dmar_rhsa {
        struct acpi_dmar_header header;
        uint32_t reserved;
        uint64_t base_address;
        uint32_t proximity_domain;
};

/* 4: ACPI Namespace Device Declaration Structure */

struct acpi_dmar_andd {
        struct acpi_dmar_header header;
        uint8_t reserved[3];
        uint8_t device_number;
        char device_name[1];
};

/* Reset to default packing */

#pragma pack()
