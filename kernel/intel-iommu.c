#define pr_fmt(fmt)     "iommu: " fmt

#include <asm/intel-iommu.h>
#include <asm/io.h>
#include <sys/acpi.h>
#include <sys/errno.h>
#include <sys/iommu.h>

#define for_each_active_iommu(i)        \
        for (i = iommus; i->reg; ++i)

#define ROOT_ENTRY_PRESENT      BIT_64(0)
#define CONTEXT_ENTRY_PRESENT   BIT_64(0)

/*
 * 0: Present
 * 1-11: Reserved
 * 12-63: Context Ptr (12 - (haw-1))
 * 64-127: Reserved
 */
struct root_entry {
        uint64_t lo;
        uint64_t hi;
};

/*
 * low 64 bits:
 * 0: present
 * 1: fault processing disable
 * 2-3: translation type
 * 12-63: address space root
 * high 64 bits:
 * 0-2: address width
 * 3-6: aval
 * 8-23: domain id
 */
struct context_entry {
        uint64_t lo;
        uint64_t hi;
};

typedef int (*dmar_res_handler_t)(struct acpi_dmar_header *, void *);

struct dmar_res_callback {
        dmar_res_handler_t cb[ACPI_DMAR_TYPE_RESERVED];
        void *arg[ACPI_DMAR_TYPE_RESERVED];
};

struct intel_iommu {
        void *reg;      /* pointer to hardware regs */
        uint64_t cap;
        uint64_t ecap;
        uint32_t gcmd;  /* holds TE, EAFL. Don't need SRTP, SFL, WBF */
};

static struct intel_iommu iommus[DMAR_UNITS_SUPPORTED];
static struct root_entry root_table[256] __aligned(SZ_4K);
static struct context_entry context_tables[256][256] __aligned(SZ_4K);

static void dmar_table_print_dmar_entry(struct acpi_dmar_header *header)
{
        struct acpi_dmar_hardware_unit *drhd;
        struct acpi_dmar_reserved_memory *rmrr;
        struct acpi_dmar_atsr *atsr;
        struct acpi_dmar_rhsa *rhsa;

        switch (header->type) {
        case ACPI_DMAR_TYPE_HARDWARE_UNIT:
                drhd = container_of(header, struct acpi_dmar_hardware_unit,
                                    header);
                pr_info("DRHD base: %#016" PRIx64 " flags: %#x\n",
                        drhd->address, drhd->flags);
                break;
        case ACPI_DMAR_TYPE_RESERVED_MEMORY:
                rmrr = container_of(header, struct acpi_dmar_reserved_memory,
                                    header);
                pr_info("RMRR base: %#016" PRIx64 " end: %#016" PRIx64 "\n",
                        rmrr->base_address, rmrr->end_address);
                break;
        case ACPI_DMAR_TYPE_ROOT_ATS:
                atsr = container_of(header, struct acpi_dmar_atsr, header);
                pr_info("ATSR flags: %#x\n", atsr->flags);
                break;
        case ACPI_DMAR_TYPE_HARDWARE_AFFINITY:
                rhsa = container_of(header, struct acpi_dmar_rhsa, header);
                pr_info("RHSA base: %#016" PRIx64 " proximity domain: %#x\n",
                        rhsa->base_address, rhsa->proximity_domain);
                break;
        case ACPI_DMAR_TYPE_NAMESPACE:
                /* We don't print this here because we need to sanity-check
                   it first. So print it in dmar_parse_one_andd() instead. */
                break;
        }
}

static int dmar_walk_dmar_table(struct acpi_table_dmar *dmar,
                                struct dmar_res_callback *cb)
{
        struct acpi_dmar_header *start, *end, *iter, *next;
        size_t len;

        start = (void *)(dmar + 1);
        len = dmar->header.length - sizeof(*dmar);
        end = (void *)start + len;

        for (iter = start; iter < end; iter = next) {
                next = (void *)iter + iter->length;
                if (iter->length == 0) {
                        /* Avoid looping forever on bad ACPI tables */
                        pr_warn("invalid 0-length structure\n");
                        break;
                } else if (next > end) {
                        /* Avoid passing table end */
                        pr_warn("record passes table end\n");
                        return -EINVAL;
                }

                dmar_table_print_dmar_entry(iter);

                if (iter->type >= ACPI_DMAR_TYPE_RESERVED) {
                        /* continue for forward compatibility */
                        pr_info("unknown DMAR structure type %d\n",
                                 iter->type);
                } else if (cb->cb[iter->type]) {
                        int ret;

                        ret = cb->cb[iter->type](iter, cb->arg[iter->type]);
                        if (ret)
                                return ret;
                }
        }

        return 0;
}

static int dmar_parse_one_drhd(struct acpi_dmar_header *header, void *arg)
{
        struct acpi_dmar_hardware_unit *drhd;
        struct intel_iommu *iommu;
        uint32_t ver;
        int count = *(int *)arg;

        drhd = (struct acpi_dmar_hardware_unit *)header;
        BUG_ON(count >= ARRAY_SIZE(iommus));
        iommu = &iommus[count];
        (*(int *)arg)++;

        iommu->reg = __va(drhd->address);

        iommu->cap = readq(iommu->reg + DMAR_CAP_REG);
        iommu->ecap = readq(iommu->reg + DMAR_ECAP_REG);

        ver = readl(iommu->reg + DMAR_VER_REG);
        pr_info("ver %d.%d cap %" PRIx64 " ecap %" PRIx64 "\n",
                DMAR_VER_MAJOR(ver), DMAR_VER_MINOR(ver),
                iommu->cap, iommu->ecap);

        /* use register-based invalidation for simplicity */
        return 0;
}

static int acpi_parse_dmar(struct acpi_table_header *table)
{
        struct acpi_table_dmar *dmar;
        int drhd_count = 0, r;
        struct dmar_res_callback cb = {
                .arg[ACPI_DMAR_TYPE_HARDWARE_UNIT] = &drhd_count,
                .cb[ACPI_DMAR_TYPE_HARDWARE_UNIT] = &dmar_parse_one_drhd,
        };

        dmar = (struct acpi_table_dmar *)table;
        r = dmar_walk_dmar_table(dmar, &cb);
        if (r == 0 && drhd_count == 0) {
                pr_warn("no DRHD structure found in DMAR table\n");
                return -ENODEV;
        }

        return r;
}

static void iommu_flush_write_buffer(struct intel_iommu *iommu)
{
        uint32_t val;

        if (!cap_rwbf(iommu->cap))
                return;

        writel(iommu->gcmd | DMA_GCMD_WBF, iommu->reg + DMAR_GCMD_REG);

        /* make sure hardware complete it */
        IOMMU_WAIT_OP(iommu, DMAR_GSTS_REG,
                      readl, (!(val & DMA_GSTS_WBFS)), val);
}

static void iommu_set_root_entry(struct intel_iommu *iommu)
{
        phys_addr_t addr;
        uint32_t sts;

        /* use legacy root table (no need for extended root table for now) */
        addr = __pa(root_table);
        writeq(addr, iommu->reg + DMAR_RTADDR_REG);

        writel(iommu->gcmd | DMA_GCMD_SRTP, iommu->reg + DMAR_GCMD_REG);

        /* make sure hardware complete it */
        IOMMU_WAIT_OP(iommu, DMAR_GSTS_REG,
                      readl, (sts & DMA_GSTS_RTPS), sts);
}

/* return value determine if we need a write buffer flush */
static void iommu_flush_context(struct intel_iommu *iommu,
                                uint16_t did, uint16_t source_id,
                                uint8_t function_mask, uint64_t type)
{
        uint64_t val = 0;

        switch (type) {
        case DMA_CCMD_GLOBAL_INVL:
                val = DMA_CCMD_GLOBAL_INVL;
                break;
        case DMA_CCMD_DOMAIN_INVL:
                val = DMA_CCMD_DOMAIN_INVL|DMA_CCMD_DID(did);
                break;
        case DMA_CCMD_DEVICE_INVL:
                val = DMA_CCMD_DEVICE_INVL|DMA_CCMD_DID(did)
                        | DMA_CCMD_SID(source_id) | DMA_CCMD_FM(function_mask);
                break;
        default:
                BUG();
        }
        val |= DMA_CCMD_ICC;

        writeq(val, iommu->reg + DMAR_CCMD_REG);

        /* make sure hardware complete it */
        IOMMU_WAIT_OP(iommu, DMAR_CCMD_REG,
                      readq, (!(val & DMA_CCMD_ICC)), val);
}

/* return value determine if we need a write buffer flush */
static void iommu_flush_iotlb(struct intel_iommu *iommu, uint16_t did,
                              uint64_t addr, unsigned int size_order,
                              uint64_t type)
{
        int tlb_offset = ecap_iotlb_offset(iommu->ecap);
        uint64_t val = 0, val_iva = 0;

        switch (type) {
        case DMA_TLB_GLOBAL_FLUSH:
                /* global flush doesn't need set IVA_REG */
                val = DMA_TLB_GLOBAL_FLUSH|DMA_TLB_IVT;
                break;
        case DMA_TLB_DSI_FLUSH:
                val = DMA_TLB_DSI_FLUSH|DMA_TLB_IVT|DMA_TLB_DID(did);
                break;
        case DMA_TLB_PSI_FLUSH:
                val = DMA_TLB_PSI_FLUSH|DMA_TLB_IVT|DMA_TLB_DID(did);
                /* IH bit is passed in as part of address */
                val_iva = size_order | addr;
                break;
        default:
                BUG();
        }

        /* Note: set drain read/write */
        if (cap_write_drain(iommu->cap))
                val |= DMA_TLB_WRITE_DRAIN;

        /* Note: Only uses first TLB reg currently */
        if (val_iva)
                writeq(val_iva, iommu->reg + tlb_offset);
        writeq(val, iommu->reg + tlb_offset + 8);

        /* make sure hardware complete it */
        IOMMU_WAIT_OP(iommu, tlb_offset + 8,
                      readq, (!(val & DMA_TLB_IVT)), val);

        /* check IOTLB invalidation granularity */
        if (DMA_TLB_IAIG(val) == 0)
                pr_err("flush IOTLB failed\n");
        if (DMA_TLB_IAIG(val) != DMA_TLB_IIRG(type))
                pr_info("TLB flush request %" PRIx64 ", actual %" PRIx64 "\n",
                        DMA_TLB_IIRG(type), DMA_TLB_IAIG(val));
}

static void iommu_enable_translation(struct intel_iommu *iommu)
{
        uint32_t sts;

        iommu->gcmd |= DMA_GCMD_TE;
        writel(iommu->gcmd, iommu->reg + DMAR_GCMD_REG);

        /* make sure hardware complete it */
        IOMMU_WAIT_OP(iommu, DMAR_GSTS_REG,
                      readl, (sts & DMA_GSTS_TES), sts);

}

static void intel_iommu_map(uint8_t bus, uint8_t devfn, phys_addr_t slptptr)
{
        /* TODO: 3- or 4-level page table */
}

static void intel_iommu_flush(void)
{
        struct intel_iommu *iommu;

        for_each_active_iommu(iommu) {
                iommu_flush_context(iommu, 0, 0, 0, DMA_CCMD_GLOBAL_INVL);
                iommu_flush_iotlb(iommu, 0, 0, 0, DMA_TLB_GLOBAL_FLUSH);
        }
}

int intel_iommu_init(void)
{
        int r;
        size_t i;
        struct intel_iommu *iommu;

        r = acpi_table_parse(ACPI_SIG_DMAR, acpi_parse_dmar);
        if (r)
                return r;

        for (i = 0; i < ARRAY_SIZE(root_table); ++i)
                root_table[i].lo = ROOT_ENTRY_PRESENT | __pa(&context_tables[i]);

        for_each_active_iommu(iommu) {
                iommu_flush_write_buffer(iommu);
                iommu_set_root_entry(iommu);
                iommu_flush_context(iommu, 0, 0, 0, DMA_CCMD_GLOBAL_INVL);
                iommu_flush_iotlb(iommu, 0, 0, 0, DMA_TLB_GLOBAL_FLUSH);
                iommu_enable_translation(iommu);
        }

        iommu_map = intel_iommu_map;
        iommu_flush = intel_iommu_flush;
        return 0;
}
