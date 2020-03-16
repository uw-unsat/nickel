#pragma once

#include <stddef.h>
#include <stdint.h>

#define SHA256_DIGEST_SIZE      32
#define SHA256_BLOCK_SIZE       64

struct sha256_ctx {
        uint32_t state[SHA256_DIGEST_SIZE / 4];
        uint64_t count;
        uint8_t buf[SHA256_BLOCK_SIZE];
};

void sha256_init(struct sha256_ctx *);
void sha256_update(struct sha256_ctx *, const uint8_t *data, unsigned int len);
void sha256_final(struct sha256_ctx *, uint8_t *out);

void sha256_digest(const void *data, size_t len, uint8_t *out);
