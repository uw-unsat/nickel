#pragma once

#include <io/compiler.h>
#include <stdint.h>

#define AES_MIN_KEY_SIZE        16
#define AES_MAX_KEY_SIZE        32
#define AES_KEYSIZE_128         16
#define AES_KEYSIZE_192         24
#define AES_KEYSIZE_256         32
#define AES_BLOCK_SIZE          16
#define AES_MAX_KEYLENGTH       (15 * 16)
#define AES_MAX_KEYLENGTH_U32   (AES_MAX_KEYLENGTH / sizeof(uint32_t))

/*
 * Please ensure that the first two fields are 16-byte aligned
 * relative to the start of the structure, i.e., don't move them!
 */
struct crypto_aes_ctx {
        uint32_t key_enc[AES_MAX_KEYLENGTH_U32];
        uint32_t key_dec[AES_MAX_KEYLENGTH_U32];
        uint32_t key_length;
} __aligned(16);

int aes_set_key(struct crypto_aes_ctx *ctx, const void *in_key, unsigned int key_len);
void aes_encrypt(struct crypto_aes_ctx *ctx, void *dst, const void *src);
void aes_decrypt(struct crypto_aes_ctx *ctx, void *dst, const void *src);

void aesni_gcm_enc(void *ctx, uint8_t *out,
                   const uint8_t *in, unsigned long plaintext_len, uint8_t *iv,
                   uint8_t *hash_subkey, const uint8_t *aad, unsigned long aad_len,
                   uint8_t *auth_tag, unsigned long auth_tag_len);

void aesni_gcm_dec(void *ctx, uint8_t *out,
                   const uint8_t *in, unsigned long ciphertext_len, uint8_t *iv,
                   uint8_t *hash_subkey, const uint8_t *aad, unsigned long aad_len,
                   uint8_t *auth_tag, unsigned long auth_tag_len);
