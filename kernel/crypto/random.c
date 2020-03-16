#include <asm/cpufeature.h>
#include <asm/tsc.h>
#include <crypto/random.h>
#include <sys/string.h>

/*
 * Use rdrand by default. Use a bogus one for QEMU testing only
 * as it doesn't have rdrand support yet.
 */

static uint64_t random_get_u64(void)
{
        uint64_t val;
        bool ok;

        while (1) {
                asm volatile("rdrand %%rax"
                             CC_SET(c)
                             : CC_OUT(c) (ok), "=a" (val));
                if (ok)
                        break;
        }

        return val;
}

void random_get_bytes(void *buf, size_t len)
{
        uint8_t *ptr = buf;
        uint64_t val;

        /* stupid workaround for QEMU/TCG */
        if (!this_cpu_has(X86_FEATURE_RDRAND)) {
                while (len) {
                        *ptr = (uint8_t)get_cycles();
                        ptr++;
                        len--;
                }
                return;
        }

        while (len >= sizeof(uint64_t)) {
                val = random_get_u64();
                memcpy(ptr, &val, sizeof(uint64_t));
                ptr += sizeof(uint64_t);
                len -= sizeof(uint64_t);
        }

        if (len > 0) {
                val = random_get_u64();
                memcpy(ptr, &val, len);
        }
}
