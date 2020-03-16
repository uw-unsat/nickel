#include <crypto/aes.h>
#include <sys/types.h>

int aesni_set_key(struct crypto_aes_ctx *ctx, const uint8_t *in_key, unsigned int key_len);
void aesni_enc(struct crypto_aes_ctx *ctx, uint8_t *dst, const uint8_t *src);
void aesni_dec(struct crypto_aes_ctx *ctx, uint8_t *dst, const uint8_t *src);

void aesni_ecb_enc(struct crypto_aes_ctx *ctx, uint8_t *out,
                   const uint8_t *in, unsigned int len);
void aesni_ecb_dec(struct crypto_aes_ctx *ctx, uint8_t *out,
                   const uint8_t *in, unsigned int len);
void aesni_cbc_enc(struct crypto_aes_ctx *ctx, uint8_t *out,
                   const uint8_t *in, unsigned int len, uint8_t *iv);
void aesni_cbc_dec(struct crypto_aes_ctx *ctx, uint8_t *out,
                   const uint8_t *in, unsigned int len, uint8_t *iv);

/*
 * ctx: AES Key schedule. Starts on a 16 byte boundary.
 * out: Ciphertext output. Encrypt in-place is allowed.
 * in: Plaintext input
 * plaintext_len: Length of data in bytes for encryption.
 * iv: Pre-counter block j0: 12 byte IV concatenated with 0x00000001.
 *     16-byte aligned pointer.
 * hash_subkey: the Hash sub key input. Data starts on a 16-byte boundary.
 * aad: Additional Authentication Data (AAD)
 * aad_len: Length of AAD in bytes.
 * auth_tag: Authenticated Tag output.
 * auth_tag_len: Authenticated Tag Length in bytes.
 *               Valid values are 16 (most likely), 12 or 8.
 */
void aesni_gcm_enc(void *ctx, uint8_t *out,
                   const uint8_t *in, unsigned long plaintext_len, uint8_t *iv,
                   uint8_t *hash_subkey, const uint8_t *aad, unsigned long aad_len,
                   uint8_t *auth_tag, unsigned long auth_tag_len);

/*
 * ctx: AES Key schedule. Starts on a 16 byte boundary.
 * out: Plaintext output. Decrypt in-place is allowed.
 * in: Ciphertext input
 * ciphertext_len, Length of data in bytes for decryption.
 * iv: Pre-counter block j0: 12 byte IV concatenated with 0x00000001.
 *     16-byte aligned pointer.
 * hash_subkey: the Hash sub key input. Data starts on a 16-byte boundary.
 * aad: Additional Authentication Data (AAD)
 * aad_len: Length of AAD in bytes. With RFC4106 this is going
 *          to be 8 or 12 bytes
 * auth_tag: Authenticated Tag output.
 * auth_tag_len: Authenticated Tag Length in bytes.
 *               Valid values are 16 (most likely), 12 or 8.
 */
void aesni_gcm_dec(void *ctx, uint8_t *out,
                   const uint8_t *in, unsigned long ciphertext_len, uint8_t *iv,
                   uint8_t *hash_subkey, const uint8_t *aad, unsigned long aad_len,
                   uint8_t *auth_tag, unsigned long auth_tag_len);


int aes_set_key(struct crypto_aes_ctx *ctx, const void *in_key, unsigned int key_len)
{
        BUG_ON(key_len != AES_KEYSIZE_128 &&
               key_len != AES_KEYSIZE_192 &&
               key_len != AES_KEYSIZE_256);

        return aesni_set_key(ctx, in_key, key_len);
}

void aes_encrypt(struct crypto_aes_ctx *ctx, void *dst, const void *src)
{
        return aesni_enc(ctx, dst, src);
}

void aes_decrypt(struct crypto_aes_ctx *ctx, void *dst, const void *src)
{
        return aesni_dec(ctx, dst, src);
}
