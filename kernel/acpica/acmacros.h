#pragma once

#include <stdint.h>

#define FALSE                           (1 == 0)
#define TRUE                            (1 == 1)

#define ACPI_LODWORD(integer64)         ((uint32_t)  (uint64_t)(integer64))
#define ACPI_HIDWORD(integer64)         ((uint32_t)(((uint64_t)(integer64)) >> 32))
#define ACPI_FORMAT_UINT64(i)           ACPI_HIDWORD(i), ACPI_LODWORD(i)
