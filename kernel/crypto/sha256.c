#include <crypto/sha.h>
#include <asm/unaligned.h>
#include <sys/bitops.h>
#include <sys/string.h>

/*
 * Interestingly, most Intel machines we have don't support the SHA
 * extension (Ryzen does, however).  Let's use plain C for now.
 */

#define SHA256_H0       0x6a09e667UL
#define SHA256_H1       0xbb67ae85UL
#define SHA256_H2       0x3c6ef372UL
#define SHA256_H3       0xa54ff53aUL
#define SHA256_H4       0x510e527fUL
#define SHA256_H5       0x9b05688cUL
#define SHA256_H6       0x1f83d9abUL
#define SHA256_H7       0x5be0cd19UL

typedef void (sha256_block_fn)(struct sha256_ctx *, uint8_t const *src, int blocks);

void sha256_init(struct sha256_ctx *sctx)
{
        sctx->state[0] = SHA256_H0;
        sctx->state[1] = SHA256_H1;
        sctx->state[2] = SHA256_H2;
        sctx->state[3] = SHA256_H3;
        sctx->state[4] = SHA256_H4;
        sctx->state[5] = SHA256_H5;
        sctx->state[6] = SHA256_H6;
        sctx->state[7] = SHA256_H7;
        sctx->count = 0;
}

static inline uint32_t Ch(uint32_t x, uint32_t y, uint32_t z)
{
        return z ^ (x & (y ^ z));
}

static inline uint32_t Maj(uint32_t x, uint32_t y, uint32_t z)
{
        return (x & y) | (z & (x | y));
}

#define e0(x)       (ror32(x, 2) ^ ror32(x,13) ^ ror32(x,22))
#define e1(x)       (ror32(x, 6) ^ ror32(x,11) ^ ror32(x,25))
#define s0(x)       (ror32(x, 7) ^ ror32(x,18) ^ (x >> 3))
#define s1(x)       (ror32(x,17) ^ ror32(x,19) ^ (x >> 10))

static inline void LOAD_OP(int I, uint32_t *W, const uint8_t *input)
{
        W[I] = get_unaligned_be32((uint32_t *)input + I);
}

static inline void BLEND_OP(int I, uint32_t *W)
{
        W[I] = s1(W[I-2]) + W[I-7] + s0(W[I-15]) + W[I-16];
}

static void sha256_transform(uint32_t *state, const uint8_t *input)
{
        uint32_t a, b, c, d, e, f, g, h, t1, t2;
        uint32_t W[64];
        int i;

        /* load the input */
        for (i = 0; i < 16; i++)
                LOAD_OP(i, W, input);

        /* now blend */
        for (i = 16; i < 64; i++)
                BLEND_OP(i, W);

        /* load the state into our registers */
        a=state[0];  b=state[1];  c=state[2];  d=state[3];
        e=state[4];  f=state[5];  g=state[6];  h=state[7];

        /* now iterate */
        t1 = h + e1(e) + Ch(e,f,g) + 0x428a2f98 + W[ 0];
        t2 = e0(a) + Maj(a,b,c);    d+=t1;    h=t1+t2;
        t1 = g + e1(d) + Ch(d,e,f) + 0x71374491 + W[ 1];
        t2 = e0(h) + Maj(h,a,b);    c+=t1;    g=t1+t2;
        t1 = f + e1(c) + Ch(c,d,e) + 0xb5c0fbcf + W[ 2];
        t2 = e0(g) + Maj(g,h,a);    b+=t1;    f=t1+t2;
        t1 = e + e1(b) + Ch(b,c,d) + 0xe9b5dba5 + W[ 3];
        t2 = e0(f) + Maj(f,g,h);    a+=t1;    e=t1+t2;
        t1 = d + e1(a) + Ch(a,b,c) + 0x3956c25b + W[ 4];
        t2 = e0(e) + Maj(e,f,g);    h+=t1;    d=t1+t2;
        t1 = c + e1(h) + Ch(h,a,b) + 0x59f111f1 + W[ 5];
        t2 = e0(d) + Maj(d,e,f);    g+=t1;    c=t1+t2;
        t1 = b + e1(g) + Ch(g,h,a) + 0x923f82a4 + W[ 6];
        t2 = e0(c) + Maj(c,d,e);    f+=t1;    b=t1+t2;
        t1 = a + e1(f) + Ch(f,g,h) + 0xab1c5ed5 + W[ 7];
        t2 = e0(b) + Maj(b,c,d);    e+=t1;    a=t1+t2;

        t1 = h + e1(e) + Ch(e,f,g) + 0xd807aa98 + W[ 8];
        t2 = e0(a) + Maj(a,b,c);    d+=t1;    h=t1+t2;
        t1 = g + e1(d) + Ch(d,e,f) + 0x12835b01 + W[ 9];
        t2 = e0(h) + Maj(h,a,b);    c+=t1;    g=t1+t2;
        t1 = f + e1(c) + Ch(c,d,e) + 0x243185be + W[10];
        t2 = e0(g) + Maj(g,h,a);    b+=t1;    f=t1+t2;
        t1 = e + e1(b) + Ch(b,c,d) + 0x550c7dc3 + W[11];
        t2 = e0(f) + Maj(f,g,h);    a+=t1;    e=t1+t2;
        t1 = d + e1(a) + Ch(a,b,c) + 0x72be5d74 + W[12];
        t2 = e0(e) + Maj(e,f,g);    h+=t1;    d=t1+t2;
        t1 = c + e1(h) + Ch(h,a,b) + 0x80deb1fe + W[13];
        t2 = e0(d) + Maj(d,e,f);    g+=t1;    c=t1+t2;
        t1 = b + e1(g) + Ch(g,h,a) + 0x9bdc06a7 + W[14];
        t2 = e0(c) + Maj(c,d,e);    f+=t1;    b=t1+t2;
        t1 = a + e1(f) + Ch(f,g,h) + 0xc19bf174 + W[15];
        t2 = e0(b) + Maj(b,c,d);    e+=t1;    a=t1+t2;

        t1 = h + e1(e) + Ch(e,f,g) + 0xe49b69c1 + W[16];
        t2 = e0(a) + Maj(a,b,c);    d+=t1;    h=t1+t2;
        t1 = g + e1(d) + Ch(d,e,f) + 0xefbe4786 + W[17];
        t2 = e0(h) + Maj(h,a,b);    c+=t1;    g=t1+t2;
        t1 = f + e1(c) + Ch(c,d,e) + 0x0fc19dc6 + W[18];
        t2 = e0(g) + Maj(g,h,a);    b+=t1;    f=t1+t2;
        t1 = e + e1(b) + Ch(b,c,d) + 0x240ca1cc + W[19];
        t2 = e0(f) + Maj(f,g,h);    a+=t1;    e=t1+t2;
        t1 = d + e1(a) + Ch(a,b,c) + 0x2de92c6f + W[20];
        t2 = e0(e) + Maj(e,f,g);    h+=t1;    d=t1+t2;
        t1 = c + e1(h) + Ch(h,a,b) + 0x4a7484aa + W[21];
        t2 = e0(d) + Maj(d,e,f);    g+=t1;    c=t1+t2;
        t1 = b + e1(g) + Ch(g,h,a) + 0x5cb0a9dc + W[22];
        t2 = e0(c) + Maj(c,d,e);    f+=t1;    b=t1+t2;
        t1 = a + e1(f) + Ch(f,g,h) + 0x76f988da + W[23];
        t2 = e0(b) + Maj(b,c,d);    e+=t1;    a=t1+t2;

        t1 = h + e1(e) + Ch(e,f,g) + 0x983e5152 + W[24];
        t2 = e0(a) + Maj(a,b,c);    d+=t1;    h=t1+t2;
        t1 = g + e1(d) + Ch(d,e,f) + 0xa831c66d + W[25];
        t2 = e0(h) + Maj(h,a,b);    c+=t1;    g=t1+t2;
        t1 = f + e1(c) + Ch(c,d,e) + 0xb00327c8 + W[26];
        t2 = e0(g) + Maj(g,h,a);    b+=t1;    f=t1+t2;
        t1 = e + e1(b) + Ch(b,c,d) + 0xbf597fc7 + W[27];
        t2 = e0(f) + Maj(f,g,h);    a+=t1;    e=t1+t2;
        t1 = d + e1(a) + Ch(a,b,c) + 0xc6e00bf3 + W[28];
        t2 = e0(e) + Maj(e,f,g);    h+=t1;    d=t1+t2;
        t1 = c + e1(h) + Ch(h,a,b) + 0xd5a79147 + W[29];
        t2 = e0(d) + Maj(d,e,f);    g+=t1;    c=t1+t2;
        t1 = b + e1(g) + Ch(g,h,a) + 0x06ca6351 + W[30];
        t2 = e0(c) + Maj(c,d,e);    f+=t1;    b=t1+t2;
        t1 = a + e1(f) + Ch(f,g,h) + 0x14292967 + W[31];
        t2 = e0(b) + Maj(b,c,d);    e+=t1;    a=t1+t2;

        t1 = h + e1(e) + Ch(e,f,g) + 0x27b70a85 + W[32];
        t2 = e0(a) + Maj(a,b,c);    d+=t1;    h=t1+t2;
        t1 = g + e1(d) + Ch(d,e,f) + 0x2e1b2138 + W[33];
        t2 = e0(h) + Maj(h,a,b);    c+=t1;    g=t1+t2;
        t1 = f + e1(c) + Ch(c,d,e) + 0x4d2c6dfc + W[34];
        t2 = e0(g) + Maj(g,h,a);    b+=t1;    f=t1+t2;
        t1 = e + e1(b) + Ch(b,c,d) + 0x53380d13 + W[35];
        t2 = e0(f) + Maj(f,g,h);    a+=t1;    e=t1+t2;
        t1 = d + e1(a) + Ch(a,b,c) + 0x650a7354 + W[36];
        t2 = e0(e) + Maj(e,f,g);    h+=t1;    d=t1+t2;
        t1 = c + e1(h) + Ch(h,a,b) + 0x766a0abb + W[37];
        t2 = e0(d) + Maj(d,e,f);    g+=t1;    c=t1+t2;
        t1 = b + e1(g) + Ch(g,h,a) + 0x81c2c92e + W[38];
        t2 = e0(c) + Maj(c,d,e);    f+=t1;    b=t1+t2;
        t1 = a + e1(f) + Ch(f,g,h) + 0x92722c85 + W[39];
        t2 = e0(b) + Maj(b,c,d);    e+=t1;    a=t1+t2;

        t1 = h + e1(e) + Ch(e,f,g) + 0xa2bfe8a1 + W[40];
        t2 = e0(a) + Maj(a,b,c);    d+=t1;    h=t1+t2;
        t1 = g + e1(d) + Ch(d,e,f) + 0xa81a664b + W[41];
        t2 = e0(h) + Maj(h,a,b);    c+=t1;    g=t1+t2;
        t1 = f + e1(c) + Ch(c,d,e) + 0xc24b8b70 + W[42];
        t2 = e0(g) + Maj(g,h,a);    b+=t1;    f=t1+t2;
        t1 = e + e1(b) + Ch(b,c,d) + 0xc76c51a3 + W[43];
        t2 = e0(f) + Maj(f,g,h);    a+=t1;    e=t1+t2;
        t1 = d + e1(a) + Ch(a,b,c) + 0xd192e819 + W[44];
        t2 = e0(e) + Maj(e,f,g);    h+=t1;    d=t1+t2;
        t1 = c + e1(h) + Ch(h,a,b) + 0xd6990624 + W[45];
        t2 = e0(d) + Maj(d,e,f);    g+=t1;    c=t1+t2;
        t1 = b + e1(g) + Ch(g,h,a) + 0xf40e3585 + W[46];
        t2 = e0(c) + Maj(c,d,e);    f+=t1;    b=t1+t2;
        t1 = a + e1(f) + Ch(f,g,h) + 0x106aa070 + W[47];
        t2 = e0(b) + Maj(b,c,d);    e+=t1;    a=t1+t2;

        t1 = h + e1(e) + Ch(e,f,g) + 0x19a4c116 + W[48];
        t2 = e0(a) + Maj(a,b,c);    d+=t1;    h=t1+t2;
        t1 = g + e1(d) + Ch(d,e,f) + 0x1e376c08 + W[49];
        t2 = e0(h) + Maj(h,a,b);    c+=t1;    g=t1+t2;
        t1 = f + e1(c) + Ch(c,d,e) + 0x2748774c + W[50];
        t2 = e0(g) + Maj(g,h,a);    b+=t1;    f=t1+t2;
        t1 = e + e1(b) + Ch(b,c,d) + 0x34b0bcb5 + W[51];
        t2 = e0(f) + Maj(f,g,h);    a+=t1;    e=t1+t2;
        t1 = d + e1(a) + Ch(a,b,c) + 0x391c0cb3 + W[52];
        t2 = e0(e) + Maj(e,f,g);    h+=t1;    d=t1+t2;
        t1 = c + e1(h) + Ch(h,a,b) + 0x4ed8aa4a + W[53];
        t2 = e0(d) + Maj(d,e,f);    g+=t1;    c=t1+t2;
        t1 = b + e1(g) + Ch(g,h,a) + 0x5b9cca4f + W[54];
        t2 = e0(c) + Maj(c,d,e);    f+=t1;    b=t1+t2;
        t1 = a + e1(f) + Ch(f,g,h) + 0x682e6ff3 + W[55];
        t2 = e0(b) + Maj(b,c,d);    e+=t1;    a=t1+t2;

        t1 = h + e1(e) + Ch(e,f,g) + 0x748f82ee + W[56];
        t2 = e0(a) + Maj(a,b,c);    d+=t1;    h=t1+t2;
        t1 = g + e1(d) + Ch(d,e,f) + 0x78a5636f + W[57];
        t2 = e0(h) + Maj(h,a,b);    c+=t1;    g=t1+t2;
        t1 = f + e1(c) + Ch(c,d,e) + 0x84c87814 + W[58];
        t2 = e0(g) + Maj(g,h,a);    b+=t1;    f=t1+t2;
        t1 = e + e1(b) + Ch(b,c,d) + 0x8cc70208 + W[59];
        t2 = e0(f) + Maj(f,g,h);    a+=t1;    e=t1+t2;
        t1 = d + e1(a) + Ch(a,b,c) + 0x90befffa + W[60];
        t2 = e0(e) + Maj(e,f,g);    h+=t1;    d=t1+t2;
        t1 = c + e1(h) + Ch(h,a,b) + 0xa4506ceb + W[61];
        t2 = e0(d) + Maj(d,e,f);    g+=t1;    c=t1+t2;
        t1 = b + e1(g) + Ch(g,h,a) + 0xbef9a3f7 + W[62];
        t2 = e0(c) + Maj(c,d,e);    f+=t1;    b=t1+t2;
        t1 = a + e1(f) + Ch(f,g,h) + 0xc67178f2 + W[63];
        t2 = e0(b) + Maj(b,c,d);    e+=t1;    a=t1+t2;

        state[0] += a; state[1] += b; state[2] += c; state[3] += d;
        state[4] += e; state[5] += f; state[6] += g; state[7] += h;

        /* clear any sensitive info... */
        a = b = c = d = e = f = g = h = t1 = t2 = 0;
        memzero_explicit(W, 64 * sizeof(uint32_t));
}

static void sha256_generic_block_fn(struct sha256_ctx *sctx, uint8_t const *src, int blocks)
{
        while (blocks--) {
                sha256_transform(sctx->state, src);
                src += SHA256_BLOCK_SIZE;
        }
}

static inline int sha256_base_do_update(struct sha256_ctx *sctx,
                                        const uint8_t *data,
                                        unsigned int len,
                                        sha256_block_fn *block_fn)
{
        unsigned int partial = sctx->count % SHA256_BLOCK_SIZE;

        sctx->count += len;

        if ((partial + len) >= SHA256_BLOCK_SIZE) {
                int blocks;

                if (partial) {
                        int p = SHA256_BLOCK_SIZE - partial;

                        memcpy(sctx->buf + partial, data, p);
                        data += p;
                        len -= p;

                        block_fn(sctx, sctx->buf, 1);
                }

                blocks = len / SHA256_BLOCK_SIZE;
                len %= SHA256_BLOCK_SIZE;

                if (blocks) {
                        block_fn(sctx, data, blocks);
                        data += blocks * SHA256_BLOCK_SIZE;
                }
                partial = 0;
        }
        if (len)
                memcpy(sctx->buf + partial, data, len);

        return 0;
}

void sha256_update(struct sha256_ctx *sctx, const uint8_t *data, unsigned int len)
{
        sha256_base_do_update(sctx, data, len, sha256_generic_block_fn);
}

static void sha256_base_do_finalize(struct sha256_ctx *sctx, sha256_block_fn *block_fn)
{
        const int bit_offset = SHA256_BLOCK_SIZE - sizeof(be64_t);
        be64_t *bits = (be64_t *)(sctx->buf + bit_offset);
        unsigned int partial = sctx->count % SHA256_BLOCK_SIZE;

        sctx->buf[partial++] = 0x80;
        if (partial > bit_offset) {
                memset(sctx->buf + partial, 0x0, SHA256_BLOCK_SIZE - partial);
                partial = 0;

                block_fn(sctx, sctx->buf, 1);
        }

        memset(sctx->buf + partial, 0x0, bit_offset - partial);
        *bits = cpu_to_be64(sctx->count << 3);
        block_fn(sctx, sctx->buf, 1);
}

static void sha256_base_finish(struct sha256_ctx *sctx, uint8_t *out)
{
        unsigned int digest_size = SHA256_DIGEST_SIZE;
        be32_t *digest = (be32_t *)out;
        int i;

        for (i = 0; digest_size > 0; i++, digest_size -= sizeof(be32_t))
                put_unaligned_be32(sctx->state[i], digest++);

        *sctx = (struct sha256_ctx){};
}

void sha256_final(struct sha256_ctx *sctx, uint8_t *out)
{
        sha256_base_do_finalize(sctx, sha256_generic_block_fn);
        sha256_base_finish(sctx, out);
}

void sha256_digest(const void *data, size_t len, uint8_t *out)
{
        struct sha256_ctx ctx;

        sha256_init(&ctx);
        while (len > SHA256_BLOCK_SIZE) {
                sha256_update(&ctx, data, SHA256_BLOCK_SIZE);
                data += SHA256_BLOCK_SIZE;
                len -= SHA256_BLOCK_SIZE;
        }
        sha256_update(&ctx, data, len);
        sha256_final(&ctx, out);
}
