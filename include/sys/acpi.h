#pragma once

#include <acpi/acconfig.h>
#include <acpi/acexcep.h>
#include <acpi/acpixf.h>
#include <acpi/actbl.h>
#include <acpi/actbl1.h>
#include <acpi/actbl2.h>
#include <acpi/actbl3.h>
#include <sys/string.h>

/* Table Handlers */
typedef int (*acpi_tbl_table_handler)(struct acpi_table_header *table);
typedef int (*acpi_tbl_entry_handler)(struct acpi_subtable_header *header,
                                      const unsigned long end);

struct acpi_subtable_proc {
        int id;
        acpi_tbl_entry_handler handler;
        int count;
};

int acpi_table_parse(char *id, acpi_tbl_table_handler handler);
int acpi_table_parse_entries_array(char *id,
                        unsigned long table_size,
                        struct acpi_subtable_proc *proc, int proc_num,
                        unsigned int max_entries);
void acpi_table_print_madt_entry(struct acpi_subtable_header *header);
