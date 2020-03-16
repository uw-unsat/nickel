#include <sys/percpu.h>
#include <sys/types.h>

uint8_t cpu_stacks[NR_CPUS][CPU_STACK_SIZE] __aligned(PAGE_SIZE);

/* %gs: 0 for BSP; SMP boot will modify this */
uint64_t initial_gs;

/* SMP boot will modify this */
uint64_t initial_stack = (uintptr_t)cpu_stacks[0] + CPU_STACK_SIZE;

unsigned long __per_cpu_offset[NR_CPUS];

DEFINE_PER_CPU(int, cpu_number);
