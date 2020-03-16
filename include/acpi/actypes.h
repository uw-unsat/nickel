#pragma once

#include <sys/string.h>
#include <stdint.h>

/* Names within the namespace are 4 bytes long */
#define ACPI_NAME_SIZE                  4
#define ACPI_PATH_SEGMENT_LENGTH        5       /* 4 chars for name + 1 char for separator */
#define ACPI_PATH_SEPARATOR             '.'

/* Sizes for ACPI table headers */
#define ACPI_OEM_ID_SIZE                6
#define ACPI_OEM_TABLE_ID_SIZE          8

/* Pointer manipulation */
#define ACPI_PTR_DIFF(a, b)             (acpi_size)((uint8_t *)(a) - (uint8_t *)(b))

/* Optimizations for 4-character (32-bit) acpi_name manipulation */
#define ACPI_COMPARE_NAME(a, b)         (!strncmp((char *)(a), (char *)(b), ACPI_NAME_SIZE))

/* Support for the special RSDP signature (8 characters) */
#define ACPI_VALIDATE_RSDP_SIG(a)       (!memcmp((char *)(a), ACPI_SIG_RSDP, 8))

typedef uint8_t acpi_owner_id;
typedef uint64_t acpi_size;
typedef uint64_t acpi_io_address;
typedef uint64_t acpi_physical_address;
typedef uint32_t acpi_status;   /* All ACPI Exceptions */
typedef uint32_t acpi_name;     /* 4-byte ACPI name */
typedef char *acpi_string;      /* Null terminated ASCII string */
typedef void *acpi_handle;      /* Actually a ptr to a NS Node */
