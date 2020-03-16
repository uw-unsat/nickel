#pragma once

#define L1_CACHE_SHIFT          6
#define L1_CACHE_BYTES          (1 << L1_CACHE_SHIFT)

#define cache_line_size()       L1_CACHE_BYTES

#define SMP_CACHE_BYTES         L1_CACHE_BYTES
#define __cacheline_aligned     __attribute__((aligned(SMP_CACHE_BYTES)))

#define ARCH_SLAB_MINALIGN      8
