#pragma once

#include <io/const.h>

/*
 * RFLAGS bits
 */
#define X86_RFLAGS_CF_BIT       0 /* Carry Flag */
#define X86_RFLAGS_CF           BIT_64(X86_RFLAGS_CF_BIT)
#define X86_RFLAGS_FIXED_BIT    1 /* Bit 1 - always on */
#define X86_RFLAGS_FIXED        BIT_64(X86_RFLAGS_FIXED_BIT)
#define X86_RFLAGS_PF_BIT       2 /* Parity Flag */
#define X86_RFLAGS_PF           BIT_64(X86_RFLAGS_PF_BIT)
#define X86_RFLAGS_AF_BIT       4 /* Auxiliary carry Flag */
#define X86_RFLAGS_AF           BIT_64(X86_RFLAGS_AF_BIT)
#define X86_RFLAGS_ZF_BIT       6 /* Zero Flag */
#define X86_RFLAGS_ZF           BIT_64(X86_RFLAGS_ZF_BIT)
#define X86_RFLAGS_SF_BIT       7 /* Sign Flag */
#define X86_RFLAGS_SF           BIT_64(X86_RFLAGS_SF_BIT)
#define X86_RFLAGS_TF_BIT       8 /* Trap Flag */
#define X86_RFLAGS_TF           BIT_64(X86_RFLAGS_TF_BIT)
#define X86_RFLAGS_IF_BIT       9 /* Interrupt Flag */
#define X86_RFLAGS_IF           BIT_64(X86_RFLAGS_IF_BIT)
#define X86_RFLAGS_DF_BIT       10 /* Direction Flag */
#define X86_RFLAGS_DF           BIT_64(X86_RFLAGS_DF_BIT)
#define X86_RFLAGS_OF_BIT       11 /* Overflow Flag */
#define X86_RFLAGS_OF           BIT_64(X86_RFLAGS_OF_BIT)
#define X86_RFLAGS_IOPL_BIT     12 /* I/O Privilege Level (2 bits) */
#define X86_RFLAGS_IOPL         (UINT64_C(3) << X86_RFLAGS_IOPL_BIT)
#define X86_RFLAGS_NT_BIT       14 /* Nested Task */
#define X86_RFLAGS_NT           BIT_64(X86_RFLAGS_NT_BIT)
#define X86_RFLAGS_RF_BIT       16 /* Resume Flag */
#define X86_RFLAGS_RF           BIT_64(X86_RFLAGS_RF_BIT)
#define X86_RFLAGS_VM_BIT       17 /* Virtual Mode */
#define X86_RFLAGS_VM           BIT_64(X86_RFLAGS_VM_BIT)
#define X86_RFLAGS_AC_BIT       18 /* Alignment Check/Access Control */
#define X86_RFLAGS_AC           BIT_64(X86_RFLAGS_AC_BIT)
#define X86_RFLAGS_VIF_BIT      19 /* Virtual Interrupt Flag */
#define X86_RFLAGS_VIF          BIT_64(X86_RFLAGS_VIF_BIT)
#define X86_RFLAGS_VIP_BIT      20 /* Virtual Interrupt Pending */
#define X86_RFLAGS_VIP          BIT_64(X86_RFLAGS_VIP_BIT)
#define X86_RFLAGS_ID_BIT       21 /* CPUID detection */
#define X86_RFLAGS_ID           BIT_64(X86_RFLAGS_ID_BIT)

/*
 * Basic CPU control in CR0
 */
#define X86_CR0_PE_BIT          0 /* Protection Enable */
#define X86_CR0_PE              BIT_64(X86_CR0_PE_BIT)
#define X86_CR0_MP_BIT          1 /* Monitor Coprocessor */
#define X86_CR0_MP              BIT_64(X86_CR0_MP_BIT)
#define X86_CR0_EM_BIT          2 /* Emulation */
#define X86_CR0_EM              BIT_64(X86_CR0_EM_BIT)
#define X86_CR0_TS_BIT          3 /* Task Switched */
#define X86_CR0_TS              BIT_64(X86_CR0_TS_BIT)
#define X86_CR0_ET_BIT          4 /* Extension Type */
#define X86_CR0_ET              BIT_64(X86_CR0_ET_BIT)
#define X86_CR0_NE_BIT          5 /* Numeric Error */
#define X86_CR0_NE              BIT_64(X86_CR0_NE_BIT)
#define X86_CR0_WP_BIT          16 /* Write Protect */
#define X86_CR0_WP              BIT_64(X86_CR0_WP_BIT)
#define X86_CR0_AM_BIT          18 /* Alignment Mask */
#define X86_CR0_AM              BIT_64(X86_CR0_AM_BIT)
#define X86_CR0_NW_BIT          29 /* Not Write-through */
#define X86_CR0_NW              BIT_64(X86_CR0_NW_BIT)
#define X86_CR0_CD_BIT          30 /* Cache Disable */
#define X86_CR0_CD              BIT_64(X86_CR0_CD_BIT)
#define X86_CR0_PG_BIT          31 /* Paging */
#define X86_CR0_PG              BIT_64(X86_CR0_PG_BIT)

/*
 * Paging options in CR3
 */
#define X86_CR3_PWT_BIT         3 /* Page Write Through */
#define X86_CR3_PWT             BIT_64(X86_CR3_PWT_BIT)
#define X86_CR3_PCD_BIT         4 /* Page Cache Disable */
#define X86_CR3_PCD             BIT_64(X86_CR3_PCD_BIT)
#define X86_CR3_PCID_MASK       UINT64_C(0x00000fff) /* PCID Mask */

/*
 * Intel CPU features in CR4
 */
#define X86_CR4_VME_BIT         0 /* enable vm86 extensions */
#define X86_CR4_VME             BIT_64(X86_CR4_VME_BIT)
#define X86_CR4_PVI_BIT         1 /* virtual interrupts flag enable */
#define X86_CR4_PVI             BIT_64(X86_CR4_PVI_BIT)
#define X86_CR4_TSD_BIT         2 /* disable time stamp at ipl 3 */
#define X86_CR4_TSD             BIT_64(X86_CR4_TSD_BIT)
#define X86_CR4_DE_BIT          3 /* enable debugging extensions */
#define X86_CR4_DE              BIT_64(X86_CR4_DE_BIT)
#define X86_CR4_PSE_BIT         4 /* enable page size extensions */
#define X86_CR4_PSE             BIT_64(X86_CR4_PSE_BIT)
#define X86_CR4_PAE_BIT         5 /* enable physical address extensions */
#define X86_CR4_PAE             BIT_64(X86_CR4_PAE_BIT)
#define X86_CR4_MCE_BIT         6 /* Machine check enable */
#define X86_CR4_MCE             BIT_64(X86_CR4_MCE_BIT)
#define X86_CR4_PGE_BIT         7 /* enable global pages */
#define X86_CR4_PGE             BIT_64(X86_CR4_PGE_BIT)
#define X86_CR4_PCE_BIT         8 /* enable performance counters at ipl 3 */
#define X86_CR4_PCE             BIT_64(X86_CR4_PCE_BIT)
#define X86_CR4_OSFXSR_BIT      9 /* enable fast FPU save and restore */
#define X86_CR4_OSFXSR          BIT_64(X86_CR4_OSFXSR_BIT)
#define X86_CR4_OSXMMEXCPT_BIT  10 /* enable unmasked SSE exceptions */
#define X86_CR4_OSXMMEXCPT      BIT_64(X86_CR4_OSXMMEXCPT_BIT)
#define X86_CR4_VMXE_BIT        13 /* enable VMX virtualization */
#define X86_CR4_VMXE            BIT_64(X86_CR4_VMXE_BIT)
#define X86_CR4_SMXE_BIT        14 /* enable safer mode (TXT) */
#define X86_CR4_SMXE            BIT_64(X86_CR4_SMXE_BIT)
#define X86_CR4_FSGSBASE_BIT    16 /* enable RDWRFSGS support */
#define X86_CR4_FSGSBASE        BIT_64(X86_CR4_FSGSBASE_BIT)
#define X86_CR4_PCIDE_BIT       17 /* enable PCID support */
#define X86_CR4_PCIDE           BIT_64(X86_CR4_PCIDE_BIT)
#define X86_CR4_OSXSAVE_BIT     18 /* enable xsave and xrestore */
#define X86_CR4_OSXSAVE         BIT_64(X86_CR4_OSXSAVE_BIT)
#define X86_CR4_SMEP_BIT        20 /* enable SMEP support */
#define X86_CR4_SMEP            BIT_64(X86_CR4_SMEP_BIT)
#define X86_CR4_SMAP_BIT        21 /* enable SMAP support */
#define X86_CR4_SMAP            BIT_64(X86_CR4_SMAP_BIT)
#define X86_CR4_PKE_BIT         22 /* enable Protection Keys support */
#define X86_CR4_PKE             BIT_64(X86_CR4_PKE_BIT)

/*
 * x86-64 Task Priority Register, CR8
 */
#define X86_CR8_TPR             UINT64_C(0x0000000f) /* task priority register */
