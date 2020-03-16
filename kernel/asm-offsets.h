/*
 * DO NOT MODIFY.
 *
 * This file was automatically generated.
 */

#pragma once

#define CPU_ENTRY_AREA_tss 8192 /* offsetof(struct cpu_entry_area, tss) */
#define CPU_ENTRY_AREA_entry_trampoline 12288 /* offsetof(struct cpu_entry_area, entry_trampoline) */
#define CPU_ENTRY_AREA_entry_stack 4096 /* offsetof(struct cpu_entry_area, entry_stack) */
#define SIZEOF_entry_stack 4096 /* sizeof(struct entry_stack) */
#define TSS_ist 36 /* offsetof(struct tss, ist) */
#define TSS_sp0 4 /* offsetof(struct tss, sp0) */
#define TSS_sp1 12 /* offsetof(struct tss, sp1) */

