#include <sys/byteorder.h>

static inline void put_unaligned_be32(uint32_t val, void *p)
{
        *((be32_t *)p) = cpu_to_be32(val);
}

static inline uint32_t get_unaligned_be32(const void *p)
{
        return be32_to_cpup((be32_t *)p);
}
