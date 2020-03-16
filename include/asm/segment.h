#pragma once

/* Simple and small GDT entries for booting only: */

#define GDT_ENTRY_BOOT_CS       2
#define GDT_ENTRY_BOOT_DS       3
#define GDT_ENTRY_BOOT_TSS      4

#define BOOT_CS                 (GDT_ENTRY_BOOT_CS * 8)
#define BOOT_DS                 (GDT_ENTRY_BOOT_DS * 8)
#define BOOT_TSS                (GDT_ENTRY_BOOT_TSS * 8)

#define GDT_ENTRY_INVALID_SEG   0

/* Regular GDT entries: */

#define GDT_ENTRY_KERNEL_CS     2
#define GDT_ENTRY_KERNEL_DS     3

/*
 * We cannot use the same code segment descriptor for user and kernel mode,
 * not even in long flat mode, because of different DPL.
 *
 * GDT layout to get 64-bit SYSCALL/SYSRET support right. SYSRET hardcodes
 * selectors:
 *
 *   if returning to 32-bit userspace: cs = STAR.SYSRET_CS,
 *   if returning to 64-bit userspace: cs = STAR.SYSRET_CS+16,
 *
 * ss = STAR.SYSRET_CS+8 (in either case)
 *
 * thus USER_DS should be between 32-bit and 64-bit code selectors:
 */
#define GDT_ENTRY_USER_DS       5
#define GDT_ENTRY_USER_CS       6

/* Needs two entries */
#define GDT_ENTRY_TSS           8

/* Number of entries in the GDT table */
#define GDT_ENTRIES             16

/*
 * Segment selector values corresponding to the above entries:
 *
 * Note, selectors also need to have a correct RPL,
 * expressed with the +3 value for user-space selectors:
 */
#define KERNEL_CS               (GDT_ENTRY_KERNEL_CS * 8)
#define KERNEL_DS               (GDT_ENTRY_KERNEL_DS * 8)
#define USER_DS                 (GDT_ENTRY_USER_DS * 8 + 3)
#define USER_CS                 (GDT_ENTRY_USER_CS * 8 + 3)

#define IDT_ENTRIES             256
#define NUM_EXCEPTION_VECTORS   32

#define GDT_SIZE                (GDT_ENTRIES * 8)
