#pragma once

#include <io/mmu.h>

#ifndef NR_CPUS
#error "NR_CPUS is not defined"
#endif

#define CPU_STACK_SIZE          (32 * PAGE_SIZE)
#define EXCEPTION_STACK_SIZE    (1 * PAGE_SIZE)

#define DOUBLEFAULT_STACK       1
#define NMI_STACK               2
#define DEBUG_STACK             3
#define MCE_STACK               4
#define NR_EXCEPTION_STACKS     4  /* hw limit: 7 */

#ifndef __ASSEMBLER__
extern uint8_t cpu_stacks[NR_CPUS][CPU_STACK_SIZE];
extern uint64_t initial_gs;
extern uint64_t initial_stack;
#endif
