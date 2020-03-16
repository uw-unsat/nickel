#pragma once

#include <sys/types.h>

extern void (*iommu_map)(uint8_t bus, uint8_t devfn, phys_addr_t slptptr);
extern void (*iommu_flush)(void);
