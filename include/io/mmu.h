#pragma once

#include <io/const.h>
#include <limits.h>

/* limits.h may define PAGE_SIZE; include it to avoid redefinition */
#ifdef PAGE_SIZE
#undef PAGE_SIZE
#endif

#define PAGE_SHIFT              12
#define PAGE_SIZE               (UINT64_C(1) << PAGE_SHIFT)
#define PAGE_MASK               (~(PAGE_SIZE - 1))

#define PHYSICAL_MASK_SHIFT     46
#define VIRTUAL_MASK_SHIFT      47

#define PHYSICAL_MASK           ((UINT64_C(1) << PHYSICAL_MASK_SHIFT) - 1)
#define VIRTUAL_MASK            ((UINT64_C(1) << VIRTUAL_MASK_SHIFT) - 1)

#define PT_SHIFT                12
#define PTRS_PER_PT             512
#define pt_index(x)             (((x) >> PT_SHIFT) & (PTRS_PER_PT - 1))

#define PD_SHIFT                21
#define PTRS_PER_PD             512
#define pd_index(x)             (((x) >> PD_SHIFT) & (PTRS_PER_PD - 1))

#define PDPT_SHIFT              30
#define PTRS_PER_PDPT           512
#define pdpt_index(x)           (((x) >> PDPT_SHIFT) & (PTRS_PER_PDPT - 1))

#define PML4_SHIFT              39
#define PTRS_PER_PML4           512
#define pml4_index(x)           (((x) >> PML4_SHIFT) & (PTRS_PER_PML4 - 1))

#define pmd_index(x)            pd_index(x)
#define pud_index(x)            pdpt_index(x)

#define MAX_PHYSMEM_BITS        46
#define MAXMEM                  (UINT64_C(1) << MAX_PHYSMEM_BITS)
#define MAXMEM_PFN              (MAXMEM >> PAGE_SHIFT)

#define PTE_BIT_PRESENT         0       /* is present */
#define PTE_BIT_RW              1       /* writeable */
#define PTE_BIT_USER            2       /* userspace addressable */
#define PTE_BIT_PWT             3       /* page write through */
#define PTE_BIT_PCD             4       /* page cache disabled */
#define PTE_BIT_ACCESSED        5       /* was accessed (raised by CPU) */
#define PTE_BIT_DIRTY           6       /* was written to (raised by CPU) */
#define PTE_BIT_PSE             7       /* 4 MB (or 2MB) page */
#define PTE_BIT_PAT             7       /* on 4KB pages */
#define PTE_BIT_GLOBAL          8       /* Global TLB entry PPro+ */
#define PTE_BIT_SOFTW1          9       /* available for programmer */
#define PTE_BIT_SOFTW2          10      /* " */
#define PTE_BIT_SOFTW3          11      /* " */
#define PTE_BIT_PAT_LARGE       12      /* On 2MB or 1GB pages */
#define PTE_BIT_SOFTW4          58      /* available for programmer */
#define PTE_BIT_PKEY_BIT0       59      /* Protection Keys, bit 1/4 */
#define PTE_BIT_PKEY_BIT1       60      /* Protection Keys, bit 2/4 */
#define PTE_BIT_PKEY_BIT2       61      /* Protection Keys, bit 3/4 */
#define PTE_BIT_PKEY_BIT3       62      /* Protection Keys, bit 4/4 */
#define PTE_BIT_NX              63      /* No execute: only valid after cpuid check */

#define PTE_PRESENT             BIT_64(PTE_BIT_PRESENT)
#define PTE_RW                  BIT_64(PTE_BIT_RW)
#define PTE_USER                BIT_64(PTE_BIT_USER)
#define PTE_PWT                 BIT_64(PTE_BIT_PWT)
#define PTE_PCD                 BIT_64(PTE_BIT_PCD)
#define PTE_ACCESSED            BIT_64(PTE_BIT_ACCESSED)
#define PTE_DIRTY               BIT_64(PTE_BIT_DIRTY)
#define PTE_PSE                 BIT_64(PTE_BIT_PSE)
#define PTE_GLOBAL              BIT_64(PTE_BIT_GLOBAL)
#define PTE_SOFTW1              BIT_64(PTE_BIT_SOFTW1)
#define PTE_SOFTW2              BIT_64(PTE_BIT_SOFTW2)
#define PTE_SOFTW3              BIT_64(PTE_BIT_SOFTW3)
#define PTE_SOFTW4              BIT_64(PTE_BIT_SOFTW4)
#define PTE_NX                  BIT_64(PTE_BIT_NX)

#define PTE_PFN_SHIFT           PAGE_SHIFT
#define PTE_PFN_MASK            (PAGE_MASK & PHYSICAL_MASK)

#define PTE_KERNEL_EXEC         (PTE_PRESENT | PTE_RW)
#define PTE_KERNEL              (PTE_KERNEL_EXEC | PTE_NX)

#define PTE_KERNEL_RO           (PTE_KERNEL & ~PTE_RW)
#define PTE_KERNEL_RX           (PTE_KERNEL_EXEC & ~PTE_RW)
