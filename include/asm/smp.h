#pragma once

#include <asm/threads.h>

/* Warm reset vector position: */
#define TRAMPOLINE_PHYS_LOW             0x467
#define TRAMPOLINE_PHYS_HIGH            0x469

extern int nr_logical_cpuids;

extern int cpuid_to_apicid[NR_CPUS];

void smp_notify(void);
int smp_find_cpu(int apicid);
