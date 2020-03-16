#pragma once

#include <sys/types.h>

struct multiboot_info;

void porte9_init(const char *prefix);
void uart8250_init(void);
void vgacon_init(void);
void kbd_init(void);
void trap_init(void);
void syscall_init(void);
void cpu_init(void);
void fpu_init(void);
void tsc_init(void);
void mtrr_init(void);
void multiboot_init(uint32_t magic, struct multiboot_info *);
void acpi_table_init(void);
void apic_init(void);
void x2apic_init(void);
void smp_init(uint32_t addr);
int iommu_init(void);
void pci_init(void);
void ns_init(void);
void e1000_init(void);
void kvm_init(void);
noreturn void kvm_bsp_run(void *tdp);
noreturn void kvm_ap_run(void *tdp);
