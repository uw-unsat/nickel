#pragma once

#include <asm/apic.h>
#include <asm/processor.h>

#define DMAR_UNITS_SUPPORTED    MAX_IO_APICS

#define VTD_PAGE_SHIFT          12
#define VTD_PAGE_SIZE           (UINT64_C(1) << VTD_PAGE_SHIFT)
#define VTD_PAGE_MASK           ((~UINT64_C(0)) << VTD_PAGE_SHIFT)
#define VTD_PAGE_ALIGN(addr)    (((addr) + VTD_PAGE_SIZE - 1) & VTD_PAGE_MASK)

#define VTD_STRIDE_SHIFT        9
#define VTD_STRIDE_MASK         ((~UINT64_C(0)) << VTD_STRIDE_SHIFT)

#define DMA_PTE_READ            BIT_64(0)
#define DMA_PTE_WRITE           BIT_64(2)
#define DMA_PTE_LARGE_PAGE      BIT_64(7)
#define DMA_PTE_SNP             BIT_64(11)

/* Intel IOMMU register specification per version 1.0 public spec */

#define DMAR_VER_REG    0x0     /* Arch version supported by this IOMMU */
#define DMAR_CAP_REG    0x8     /* Hardware supported capabilities */
#define DMAR_ECAP_REG   0x10    /* Extended capabilities supported */
#define DMAR_GCMD_REG   0x18    /* Global command register */
#define DMAR_GSTS_REG   0x1c    /* Global status register */
#define DMAR_RTADDR_REG 0x20    /* Root entry table */
#define DMAR_CCMD_REG   0x28    /* Context command reg */
#define DMAR_FSTS_REG   0x34    /* Fault Status register */
#define DMAR_FECTL_REG  0x38    /* Fault control register */
#define DMAR_FEDATA_REG 0x3c    /* Fault event interrupt data register */
#define DMAR_FEADDR_REG 0x40    /* Fault event interrupt addr register */
#define DMAR_FEUADDR_REG 0x44   /* Upper address register */
#define DMAR_AFLOG_REG  0x58    /* Advanced Fault control */
#define DMAR_PMEN_REG   0x64    /* Enable Protected Memory Region */
#define DMAR_PLMBASE_REG 0x68   /* PMRR Low addr */
#define DMAR_PLMLIMIT_REG 0x6c  /* PMRR low limit */
#define DMAR_PHMBASE_REG 0x70   /* pmrr high base addr */
#define DMAR_PHMLIMIT_REG 0x78  /* pmrr high limit */
#define DMAR_IQH_REG    0x80    /* Invalidation queue head register */
#define DMAR_IQT_REG    0x88    /* Invalidation queue tail register */
#define DMAR_IQ_SHIFT   4       /* Invalidation queue head/tail shift */
#define DMAR_IQA_REG    0x90    /* Invalidation queue addr register */
#define DMAR_ICS_REG    0x9c    /* Invalidation complete status register */
#define DMAR_IRTA_REG   0xb8    /* Interrupt remapping table addr register */
#define DMAR_PQH_REG    0xc0    /* Page request queue head register */
#define DMAR_PQT_REG    0xc8    /* Page request queue tail register */
#define DMAR_PQA_REG    0xd0    /* Page request queue address register */
#define DMAR_PRS_REG    0xdc    /* Page request status register */
#define DMAR_PECTL_REG  0xe0    /* Page request event control register */
#define DMAR_PEDATA_REG 0xe4    /* Page request event interrupt data register */
#define DMAR_PEADDR_REG 0xe8    /* Page request event interrupt addr register */
#define DMAR_PEUADDR_REG 0xec   /* Page request event Upper address register */

#define DMAR_VER_MAJOR(v)               (((v) & 0xf0) >> 4)
#define DMAR_VER_MINOR(v)               ((v) & 0x0f)

/* Decoding Capability Register */

#define cap_pi_support(c)       (((c) >> 59) & 1)
#define cap_read_drain(c)       (((c) >> 55) & 1)
#define cap_write_drain(c)      (((c) >> 54) & 1)
#define cap_max_amask_val(c)    (((c) >> 48) & 0x3f)
#define cap_num_fault_regs(c)   ((((c) >> 40) & 0xff) + 1)
#define cap_pgsel_inv(c)        (((c) >> 39) & 1)

#define cap_super_page_val(c)   (((c) >> 34) & 0xf)
#define cap_super_offset(c)     (((find_first_bit(&cap_super_page_val(c), 4)) \
                                        * OFFSET_STRIDE) + 21)

#define cap_fault_reg_offset(c) ((((c) >> 24) & 0x3ff) * 16)
#define cap_max_fault_reg_offset(c) \
        (cap_fault_reg_offset(c) + cap_num_fault_regs(c) * 16)

#define cap_zlr(c)              (((c) >> 22) & 1)
#define cap_isoch(c)            (((c) >> 23) & 1)
#define cap_mgaw(c)             ((((c) >> 16) & 0x3f) + 1)
#define cap_sagaw(c)            (((c) >> 8) & 0x1f)
#define cap_caching_mode(c)     (((c) >> 7) & 1)
#define cap_phmr(c)             (((c) >> 6) & 1)
#define cap_plmr(c)             (((c) >> 5) & 1)
#define cap_rwbf(c)             (((c) >> 4) & 1)
#define cap_afl(c)              (((c) >> 3) & 1)
#define cap_ndoms(c)            (((unsigned long)1) << (4 + 2 * ((c) & 0x7)))

/* Extended Capability Register */

#define ecap_pasid(e)           ((e >> 40) & 0x1)
#define ecap_pss(e)             ((e >> 35) & 0x1f)
#define ecap_eafs(e)            ((e >> 34) & 0x1)
#define ecap_nwfs(e)            ((e >> 33) & 0x1)
#define ecap_srs(e)             ((e >> 31) & 0x1)
#define ecap_ers(e)             ((e >> 30) & 0x1)
#define ecap_prs(e)             ((e >> 29) & 0x1)
#define ecap_broken_pasid(e)    ((e >> 28) & 0x1)
#define ecap_dis(e)             ((e >> 27) & 0x1)
#define ecap_nest(e)            ((e >> 26) & 0x1)
#define ecap_mts(e)             ((e >> 25) & 0x1)
#define ecap_ecs(e)             ((e >> 24) & 0x1)
#define ecap_iotlb_offset(e)    ((((e) >> 8) & 0x3ff) * 16)
#define ecap_max_iotlb_offset(e) (ecap_iotlb_offset(e) + 16)
#define ecap_coherent(e)        ((e) & 0x1)
#define ecap_qis(e)             ((e) & 0x2)
#define ecap_pass_through(e)    ((e >> 6) & 0x1)
#define ecap_eim_support(e)     ((e >> 4) & 0x1)
#define ecap_ir_support(e)      ((e >> 3) & 0x1)
#define ecap_dev_iotlb_support(e)       (((e) >> 2) & 0x1)
#define ecap_max_handle_mask(e) ((e >> 20) & 0xf)
#define ecap_sc_support(e)      ((e >> 7) & 0x1) /* Snooping Control */

/* IOTLB_REG */
#define DMA_TLB_FLUSH_GRANU_OFFSET  60
#define DMA_TLB_GLOBAL_FLUSH (((uint64_t)1) << 60)
#define DMA_TLB_DSI_FLUSH (((uint64_t)2) << 60)
#define DMA_TLB_PSI_FLUSH (((uint64_t)3) << 60)
#define DMA_TLB_IIRG(type) ((type >> 60) & 3)
#define DMA_TLB_IAIG(val) (((val) >> 57) & 3)
#define DMA_TLB_READ_DRAIN (((uint64_t)1) << 49)
#define DMA_TLB_WRITE_DRAIN (((uint64_t)1) << 48)
#define DMA_TLB_DID(id) (((uint64_t)((id) & 0xffff)) << 32)
#define DMA_TLB_IVT (((uint64_t)1) << 63)
#define DMA_TLB_IH_NONLEAF (((uint64_t)1) << 6)
#define DMA_TLB_MAX_SIZE (0x3f)

/* INVALID_DESC */
#define DMA_CCMD_INVL_GRANU_OFFSET  61
#define DMA_ID_TLB_GLOBAL_FLUSH (((uint64_t)1) << 4)
#define DMA_ID_TLB_DSI_FLUSH    (((uint64_t)2) << 4)
#define DMA_ID_TLB_PSI_FLUSH    (((uint64_t)3) << 4)
#define DMA_ID_TLB_READ_DRAIN   (((uint64_t)1) << 7)
#define DMA_ID_TLB_WRITE_DRAIN  (((uint64_t)1) << 6)
#define DMA_ID_TLB_DID(id)      (((uint64_t)((id & 0xffff) << 16)))
#define DMA_ID_TLB_IH_NONLEAF   (((uint64_t)1) << 6)
#define DMA_ID_TLB_ADDR(addr)   (addr)
#define DMA_ID_TLB_ADDR_MASK(mask)      (mask)

/* PMEN_REG */
#define DMA_PMEN_EPM (((uint32_t)1)<<31)
#define DMA_PMEN_PRS (((uint32_t)1)<<0)

/* GCMD_REG */
#define DMA_GCMD_TE (((uint32_t)1) << 31)
#define DMA_GCMD_SRTP (((uint32_t)1) << 30)
#define DMA_GCMD_SFL (((uint32_t)1) << 29)
#define DMA_GCMD_EAFL (((uint32_t)1) << 28)
#define DMA_GCMD_WBF (((uint32_t)1) << 27)
#define DMA_GCMD_QIE (((uint32_t)1) << 26)
#define DMA_GCMD_SIRTP (((uint32_t)1) << 24)
#define DMA_GCMD_IRE (((uint32_t) 1) << 25)
#define DMA_GCMD_CFI (((uint32_t) 1) << 23)

/* GSTS_REG */
#define DMA_GSTS_TES (((uint32_t)1) << 31)
#define DMA_GSTS_RTPS (((uint32_t)1) << 30)
#define DMA_GSTS_FLS (((uint32_t)1) << 29)
#define DMA_GSTS_AFLS (((uint32_t)1) << 28)
#define DMA_GSTS_WBFS (((uint32_t)1) << 27)
#define DMA_GSTS_QIES (((uint32_t)1) << 26)
#define DMA_GSTS_IRTPS (((uint32_t)1) << 24)
#define DMA_GSTS_IRES (((uint32_t)1) << 25)
#define DMA_GSTS_CFIS (((uint32_t)1) << 23)

/* DMA_RTADDR_REG */
#define DMA_RTADDR_RTT (((uint64_t)1) << 11)

/* CCMD_REG */
#define DMA_CCMD_ICC (((uint64_t)1) << 63)
#define DMA_CCMD_GLOBAL_INVL (((uint64_t)1) << 61)
#define DMA_CCMD_DOMAIN_INVL (((uint64_t)2) << 61)
#define DMA_CCMD_DEVICE_INVL (((uint64_t)3) << 61)
#define DMA_CCMD_FM(m) (((uint64_t)((m) & 0x3)) << 32)
#define DMA_CCMD_MASK_NOBIT 0
#define DMA_CCMD_MASK_1BIT 1
#define DMA_CCMD_MASK_2BIT 2
#define DMA_CCMD_MASK_3BIT 3
#define DMA_CCMD_SID(s) (((uint64_t)((s) & 0xffff)) << 16)
#define DMA_CCMD_DID(d) ((uint64_t)((d) & 0xffff))

/* FECTL_REG */
#define DMA_FECTL_IM (((uint32_t)1) << 31)

/* FSTS_REG */
#define DMA_FSTS_PPF ((uint32_t)2)
#define DMA_FSTS_PFO ((uint32_t)1)
#define DMA_FSTS_IQE (1 << 4)
#define DMA_FSTS_ICE (1 << 5)
#define DMA_FSTS_ITE (1 << 6)
#define DMA_FSTS_PRO (1 << 7)
#define dma_fsts_fault_record_index(s) (((s) >> 8) & 0xff)

/* FRCD_REG, 32 bits access */
#define DMA_FRCD_F (((uint32_t)1) << 31)
#define dma_frcd_type(d) ((d >> 30) & 1)
#define dma_frcd_fault_reason(c) (c & 0xff)
#define dma_frcd_source_id(c) (c & 0xffff)
/* low 64 bit */
#define dma_frcd_page_addr(d) (d & (((uint64_t)-1) << PAGE_SHIFT))

/* PRS_REG */
#define DMA_PRS_PPR     ((uint32_t)1)

#define IOMMU_WAIT_OP(iommu, offset, op, cond, sts)                     \
do {                                                                    \
        while (1) {                                                     \
                sts = op(iommu->reg + offset);                          \
                if (cond)                                               \
                        break;                                          \
                cpu_relax();                                            \
        }                                                               \
} while (0)

int intel_iommu_init(void);
