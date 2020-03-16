#include <crypto/aes.h>
#include <crypto/random.h>
#include <sys/errno.h>
#include <sys/string.h>
#include "assume.h"
#include "label.h"
#include "thread.h"

static struct crypto_aes_ctx aes128_ctx;

void tag_init(void)
{
        uint8_t key[AES_KEYSIZE_128];

        random_get_bytes(key, sizeof(key));
        aes_set_key(&aes128_ctx, key, sizeof(key));
}

noinline void tag_encrypt(tag_t *dst, unsigned __int128 *src)
{
        aes_encrypt(&aes128_ctx, dst, src);
}

tag_t tag_alloc(void)
{
        page_id_t tid;
        struct page *page;
        unsigned __int128 ktag;
        tag_t utag;

        tid = get_current_thread();
        page = page_get(tid);

        utag = __tag(0);
        ktag = page->tag_counter;
        page->tag_counter++;
        ktag = (ktag << 64) | page_id_val(tid);
        tag_encrypt(&utag, &ktag);

        return utag;
}

noinline struct label *get_label(page_id_t id)
{
        BUG_ON(!page_is_type(id, PAGE_TYPE_LABEL));
        return page_data(id);
}

noinline void set_label(page_id_t id, struct label *new)
{
        struct label *la = get_label(id);
        memcpy(la->tags, new->tags, sizeof(la->tags));
}

int untyped_to_label(page_id_t id)
{
        struct page *page;
        struct label *label;
        BUILD_BUG_ON(sizeof(struct label) != PAGE_DATA_SIZE);

        page = page_get(id);
        if (page->type != PAGE_TYPE_UNTYPED)
                return -EINVAL;

        page->secrecy = LABEL_EMPTY;
        page->integrity = LABEL_EMPTY;

        page->type = PAGE_TYPE_LABEL;
        label = page_data(id);
        memset(tag_ptr(label->tags), 0xff, sizeof(label->tags));
        return 0;
}

int label_alloc(page_id_t id)
{
        int r;
        r = page_alloc(id, PAGE_TYPE_UNTYPED);
        if (r)
                return r;
        return untyped_to_label(id);
}

int label_add(page_id_t id, size_t slot, tag_t tag)
{
        struct label *label;

        BUG_ON(!page_is_type(id, PAGE_TYPE_LABEL));

        if (!(slot < LABEL_NR_TAGS))
                return -EINVAL;

        label = page_data(id);
        /* must be free */
        if (tag_is_valid(label->tags[slot]))
                return -EINVAL;

        label->tags[slot] = tag;
        return 0;
}


long labelx_add(struct label *la, tag_t tag)
{
        size_t slot;
        for (slot = 0; slot < LABEL_NR_TAGS; slot++)
                if (!tag_is_valid(la->tags[slot])) {
                        la->tags[slot] = tag;
                        return 0;
                }

        return -ENOMEM;
}

noinline struct label *make_label(uint64_t *buf)
{
        return (struct label*)buf;
}

noinline bool label_has(struct label *la, tag_t tag)
{
        size_t i;

        BUG_ON(!tag_is_valid(tag));

        for (i = 0; i < LABEL_NR_TAGS; i++) {
                if (!tag_is_valid(la->tags[i]))
                        break;
                if (safe_equal(tag, la->tags[i], tag))
                        return true;
        }
        return false;
}

noinline bool label_is_subset(struct label *la, struct label *lb)
{
        size_t i;

        for (i = 0; i < LABEL_NR_TAGS; ++i) {
                if (!tag_is_valid(la->tags[i]))
                        return true;
                if (!label_has(lb, la->tags[i]))
                        return false;
        }
        return true;
}

noinline bool label_is_subsetx(struct label *la, struct label *lb, struct label *lx)
{
        size_t i;

        for (i = 0; i < LABEL_NR_TAGS; ++i) {
                if (!tag_is_valid(la->tags[i]))
                        return true;
                if (!label_has(lx, la->tags[i]) &&
                    !label_has(lb, la->tags[i]))
                        return false;
        }
        return true;
}

noinline bool labelp_has(page_id_t id, tag_t tag)
{
        struct label *label;

        if (safe_equal(page_id, id, LABEL_EMPTY))
            return false;

        BUG_ON(!page_is_type(id, PAGE_TYPE_LABEL));
        BUG_ON(!tag_is_valid(tag));

        label = page_data(id);
        return label_has(label, tag);
}


/* check if a - x ⊆ b - x */
noinline bool labelp_is_subsetx(page_id_t a, page_id_t b, page_id_t x)
{
        struct label *la, *lb, *lx;

        if (safe_equal(page_id, a, LABEL_EMPTY))
                return true;

        BUG_ON(!page_is_type(a, PAGE_TYPE_LABEL));
        BUG_ON(!page_is_type(b, PAGE_TYPE_LABEL));
        BUG_ON(!page_is_type(x, PAGE_TYPE_LABEL));

        la = page_data(a);
        lb = page_data(b);
        lx = page_data(x);

        return label_is_subsetx(la, lb, lx);
}

/* check if a ⊆ b */
noinline bool labelp_is_subset(page_id_t a, page_id_t b)
{
        return labelp_is_subsetx(a, b, LABEL_EMPTY);
}
