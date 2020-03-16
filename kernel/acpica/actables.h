#pragma once

#include <sys/acpi.h>
#include "acmacros.h"

/*
 * tbxfroot - Root pointer utilities
 */
uint32_t acpi_tb_get_rsdp_length(struct acpi_table_rsdp *rsdp);

acpi_status acpi_tb_validate_rsdp(struct acpi_table_rsdp *rsdp);

uint8_t *acpi_tb_scan_memory_for_rsdp(uint8_t *start_address, uint32_t length);

/*
 * tbutils - table manager utilities
 */
void acpi_tb_print_table_header(acpi_physical_address address,
                                struct acpi_table_header *header);

acpi_status acpi_tb_verify_checksum(struct acpi_table_header *table, uint32_t length);

uint8_t acpi_tb_checksum(uint8_t *buffer, uint32_t length);

acpi_status acpi_tb_parse_root_table(acpi_physical_address rsdp_address);
