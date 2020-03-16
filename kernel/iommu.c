#include <asm/intel-iommu.h>
#include <sys/iommu.h>

void (*iommu_map)(uint8_t bus, uint8_t devfn, phys_addr_t slptptr);
void (*iommu_flush)(void);

void iommu_init(void)
{
        intel_iommu_init();
}
