#define _GNU_SOURCE
#include <backtrace.h>
#include <errno.h>
#include <nistar/ulib.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdnoreturn.h>
#include <string.h>
#include <sys/stat.h>

#define check(a) {{ long ret = (a); ASSERT_MSG(ret == 0, "ERRNO %d\n", ret); }}

/* label */
static ssize_t label_find_tag(struct label *la, tag_t tag)
{
        size_t i;
        for (i = 0; i < LABEL_NR_TAGS; i++) {
                if (la->tags[i] == tag)
                        return i;
        }
        return -1;
}

static ssize_t label_find_slot(struct label *la, tag_t tag)
{
        long r = -1;
        size_t i;
        for (i = 0; i < LABEL_NR_TAGS; i++) {
                if (la->tags[i] == TAG_INVALID && r < 0)
                        r = i;
                if (la->tags[i] == tag)
                        return i;
        }
        return r;
}

void label_init(struct label *la)
{
        memset(la->tags, 0xff, sizeof(la->tags));
}

long label_add_tag(struct label *la, tag_t tag)
{
        int slot = label_find_slot(la, tag);
        ASSERT_MSG(slot >= 0, "label full");
        if (la->tags[slot] != tag) {
                ASSERT_MSG(la->tags[slot] == TAG_INVALID, "label_find_slot");
                la->tags[slot] = tag;
        }
        return 0;
}

long label_remove_tag(struct label *la, tag_t tag)
{
        int slot = label_find_tag(la, tag);
        if (slot < 0)
                return 0;
        if (slot + 1 == LABEL_NR_TAGS) {
                la->tags[slot] = TAG_INVALID;;
                return 0;
        }
        memmove(&la->tags[slot], &la->tags[slot+1],
                sizeof(tag_t) * (LABEL_NR_TAGS - slot - 1));
        return 0;
}

void label_copy(struct label *la, struct label *lb)
{
        memcpy(la->tags, lb->tags, sizeof(la->tags));
}

long label_union(struct label *la, struct label *lb)
{
        int r;
        size_t i;
        for (i = 0; i < LABEL_NR_TAGS; i++) {
                r = label_add_tag(la, lb->tags[i]);
                if (r)
                        return r;
        }
        return 0;
}

long label_intersection(struct label *la, struct label *lb)
{
        size_t i;
        for (i = 0; i < LABEL_NR_TAGS; i++) {
                if (label_find_tag(lb, la->tags[i]) < 0)
                        la->tags[i] = TAG_INVALID;

        }
        return 0;
}

long label_subtract(struct label *la, struct label *lb)
{
        int r;
        size_t i;
        for (i = 0; i < LABEL_NR_TAGS; i++) {
                r = label_remove_tag(la, lb->tags[i]);
                if (r)
                        return r;
        }
        return 0;
}

bool label_is_subset(struct label *la, struct label *lb)
{
        size_t i;
        for (i = 0; i < LABEL_NR_TAGS; i++) {
                if (la->tags[i] != TAG_INVALID && label_find_tag(lb, la->tags[i]) < 0)
                        return false;

        }
        return true;
}

bool label_is_subsetx(struct label *la, struct label *lb, struct label *lx)
{
        size_t i;
        for (i = 0; i < LABEL_NR_TAGS; i++) {
                if (la->tags[i] != TAG_INVALID &&
                    label_find_tag(lx, la->tags[i]) < 0 &&
                    label_find_tag(lb, la->tags[i]) < 0)
                        return false;

        }
        return true;
}

void label_format(struct label *la, char *buf, size_t size)
{
        if (size > 1)
                buf[0] = 0;
        char tagbuf[64];
        size_t i;
        int first;
        strlcat(buf, "{", size);
        first = 1;
        for(i = 0; i < LABEL_NR_TAGS; i++) {
                if (la->tags[i] != TAG_INVALID) {
                        snprintf(tagbuf, 64, "%016lx:%016lx", (uint64_t)(la->tags[i] >> 64), (uint64_t)la->tags[i]);
                        if (!first) {
                                strlcat(buf, ", ", size);
                        }
                        strlcat(buf, tagbuf, size);
                        first = 0;

                } else {
                        break;
                }
        }
        strlcat(buf, "}", size);
}

// container

long container_get_slot(usymlink_t cont, size_t slot, usymlink_t *obj)
{
        long r;
        if ((r = sys_container_get_slot(cont.upage, slot, &obj->upage)) == 0) {
                obj->uparent = cont.upage;
                obj->uparent_slot = slot;
                return 0;
        }
        return r;
}

long container_find_by_name(usymlink_t cont, const char *name, usymlink_t *res)
{
        unsigned long n;
        usymlink_t sres;
        char sname[PAGE_NAME_LEN];

        for (n = 0; n < CONTAINER_NR_PAGES; n++) {
                if (container_get_slot(cont, n, &sres) != 0)
                        continue;
                if (page_get_name(sres, sname) != 0)
                        continue;
                if (strcmp(name, sname) == 0) {
                        *res = sres;
                        return 0;
                }
        }
        return -1;
}

static long container_find_slot(usymlink_t *obj)
{
        long r = 0;
        size_t i;
        upage_id_t uobj;
        for (i = 0; i < CONTAINER_NR_PAGES; i++) {
                if ((r = sys_container_get_slot(obj->uparent, i, &uobj)) == 0) {
                        if (obj->upage == uobj) {
                                obj->uparent_slot = i;
                                return 0;
                        }
                }
        }
        return r;
}

static ssize_t find_free_container_slot(upage_id_t ucont)
{
        size_t i;
        upage_id_t uobj;
        for (i = 0; i < CONTAINER_NR_PAGES; i++)
                if (sys_container_get_slot(ucont, i, &uobj) != 0)
                        return i;
        ASSERT_MSG(0, "find_free_slot");
        return -1;
}

ssize_t find_free_directory_slot(usymlink_t udir)
{
        size_t i;
        usymlink_t uobj;
        for (i = 0; i < DIRECTORY_NR_ENTRIES; i++)
                if (directory_get_slot(udir, i, &uobj) != 0)
                        return i;
        ASSERT_MSG(0, "find_free_slot");
        return -1;
}

/* container */

usymlink_t container_get_root(void)
{
        static usymlink_t root = USYMLINK_INVALID;

        if (!usymlink_is_valid(root)) {
                long r;
                upage_id_t uobj;

                r = sys_container_get_root(&uobj);
                ASSERT_MSG(r == 0, "sys_container_get_root");
                root.upage = uobj;
                root.uparent = uobj;
                ASSERT_MSG(usymlink_is_valid(root), "sys_container_get_root");
        }

        return root;
}

long container_get_quota(usymlink_t ucon, uint64_t *quota)
{
        long r;
        uint64_t q;
        r = sys_container_get_quota(ucon.upage, &q);
        if (r == 0)
                *quota = q;
        return r;
}

long container_get_uquota(usymlink_t ucon, uint64_t *quota)
{
        long r;
        uint64_t q;
        r = sys_container_get_uquota(ucon.upage, &q);
        if (r == 0)
                *quota = q;
        return r;
}

long container_get_qquota(usymlink_t ucon, uint64_t *quota)
{
        long r;
        uint64_t q;
        r = sys_container_get_qquota(ucon.upage, &q);
        if (r == 0)
                *quota = q;
        return r;
}

long container_move_quota(usymlink_t c1, usymlink_t c2, size_t amount)
{
        while (amount--) {
                check(sys_container_move_quota(c1.upage, c2.upage));
        }
        return 0;
}

long container_move_uquota(usymlink_t c1, usymlink_t c2, size_t amount)
{
        while (amount--) {
                check(sys_container_move_uquota(c1.upage, c2.upage));
        }
        return 0;
}

static quantum_id_t _qid = 0;
static quantum_id_t next_qid()
{
    quantum_id_t q = _qid;
    _qid = (_qid + 1) % SCHED_NR_QUANTA;
    return q;
}

long container_move_qquota(usymlink_t c1, usymlink_t c2, size_t amount)
{
        long r = 0;
        while (amount--) {
            while (1) {
                r = sys_container_move_qquota(c1.upage, next_qid(), c2.upage);
                if (r != -ENOENT)
                    break;
            }
            check(r);
        }
        return 0;
}

long reserve_page(usymlink_t *page, usymlink_t ucon)
{
        int r;
        size_t slot;
        slot = find_free_container_slot(ucon.upage);
        if ((r = sys_reserve_page(ucon.upage, slot)) != 0) {
                ASSERT_MSG(r == 0, "sys_reserve_page: %d", r);
                return r;
        }
        if ((r = sys_container_get_slot(ucon.upage, slot, &page->upage)) != 0) {
                ASSERT_MSG(r == 0, "sys_container_get_slot");
                return r;
        }
        page->uparent = ucon.upage;
        page->uparent_slot = slot;
        return r;
}

/* thread */

long thread_get_state(usymlink_t thread)
{
        return sys_thread_get_state(thread.uparent, thread.uparent_slot);
}

/* self */

usymlink_t self_get()
{
        long r;
        usymlink_t self;
        r = sys_self_get(&self);
        ASSERT_MSG(r == 0, "self_get_pud");
        r = container_find_slot(&self);
        ASSERT_MSG(r == 0, "container_find_slot");
        return self;
}

usymlink_t self_get_pud()
{
        /* This used to be static, but that caused bugs with fork.
           TODO: cache this in a static but reset after fork? */
        usymlink_t pud = USYMLINK_INVALID;
        if (!usymlink_is_valid(pud)) {
                long r;
                usymlink_t stack_upud;
                r = sys_self_get_pud(&stack_upud);
                ASSERT_MSG(r == 0, "self_get_pud");
                r = container_find_slot(&stack_upud);
                ASSERT_MSG(r == 0, "container_find_slot");
                pud = stack_upud;
        }
        return pud;
}

long self_get_label(struct label *secrecy, struct label *integrity, struct label *ownership)
{
        struct label osecrecy, ointegrity, oownership;
        if (!secrecy)
                secrecy = &osecrecy;
        if (!integrity)
                integrity = &ointegrity;
        if (!ownership)
                ownership = &oownership;

        long r;
        r = sys_self_get_label(secrecy->tags, integrity->tags, ownership->tags);
        ASSERT_MSG(r == 0, "sys_self_get_label");
        return r;
}

long self_set_label(struct label *secrecy, struct label *integrity, struct label *ownership)
{
        struct label osecrecy, ointegrity, oownership;
        if (!secrecy || !integrity || !ownership)
                self_get_label(&osecrecy, &ointegrity, &oownership);

        if (!secrecy)
                secrecy = &osecrecy;
        if (!integrity)
                integrity = &ointegrity;
        if (!ownership)
                ownership = &oownership;

        long r;
        r = sys_self_set_label(secrecy->tags, integrity->tags, ownership->tags);
        ASSERT_MSG(r == 0, "sys_self_set_label");
        return r;
}

/* page */

long page_get_container(usymlink_t usym, usymlink_t *parent)
{
        long r;
        upage_id_t cont;
        r = sys_container_get_parent(usym.uparent, &cont);
        ASSERT_MSG(r == 0, "sys_container_get_parent");
        if (r < 0)
                return r;

        parent->upage = usym.uparent;
        parent->uparent = cont;

        // populate child slot
        r = container_find_slot(parent);
        ASSERT_MSG(r == 0, "container_find_slot");
        if (r < 0)
                return r;

        return 0;
}

long page_get_type(usymlink_t usym, uint64_t *type)
{
        long r;
        uint64_t stype;
        ASSERT_MSG(usym.uparent_slot < CONTAINER_NR_PAGES, "page_get_type");
        r = sys_page_get_type(usym.uparent, usym.uparent_slot, &stype);
        if (r == 0)
                *type = stype;
        return r;
}

long page_get_name(usymlink_t usym, char name[PAGE_NAME_LEN])
{
        long r;
        // Stack allocate the name
        char sname[PAGE_NAME_LEN];
        ASSERT_MSG(usym.uparent_slot < CONTAINER_NR_PAGES, "page_get_name");
        r = sys_page_get_name(usym.uparent, usym.uparent_slot, sname);
        if (r == 0)
                strncpy(name, sname, PAGE_NAME_LEN);
        return r;
}

long page_set_name(usymlink_t usym, const char name[PAGE_NAME_LEN])
{
        // Stack allocate the name
        char sname[PAGE_NAME_LEN];
        strncpy(sname, name, PAGE_NAME_LEN);
        ASSERT_MSG(usym.uparent_slot < CONTAINER_NR_PAGES, "page_set_name");
        return sys_page_set_name(usym.uparent, usym.uparent_slot, sname);
}

long page_get_metadata(usymlink_t usym, char metadata[PAGE_METADATA_LEN])
{
        // Stack allocate the metadata
        char smetadata[PAGE_METADATA_LEN];
        ASSERT_MSG(usym.uparent_slot < CONTAINER_NR_PAGES, "page_get_metadata");
        check(sys_page_get_metadata(usym.uparent, usym.uparent_slot, smetadata));
        memcpy(metadata, smetadata, PAGE_METADATA_LEN);
        return 0;
}

long page_set_metadata(usymlink_t usym, const char metadata[PAGE_METADATA_LEN])
{
        long r;
        // Stack allocate the metadata
        char smetadata[PAGE_METADATA_LEN];
        memcpy(smetadata, metadata, PAGE_METADATA_LEN);
        ASSERT_MSG(usym.uparent_slot < CONTAINER_NR_PAGES, "page_set_metadata");
        r = sys_page_set_metadata(usym.uparent, usym.uparent_slot, smetadata);
        if (r == -EACCES)
                return r;
        ASSERT_MSG(r == 0, "page_set_metadata");
        return r;
}

long page_get_label(usymlink_t usym, struct label *la_secrecy, struct label *la_integrity)
{
        ASSERT_MSG(usym.uparent_slot < CONTAINER_NR_PAGES, "page_get_label");
        return sys_page_get_label(usym.uparent, usym.uparent_slot, la_secrecy->tags, la_integrity->tags);
}

long alloc_quantum(usymlink_t ucon, usymlink_t thread)
{
    long r;
        while (1) {
            r = sys_alloc_quantum(ucon.upage, next_qid(), thread.upage);
            if (r != -ENOENT)
                break;
        }
        ASSERT_MSG(r == 0, "alloc_quantum: %ld", r);
        return r;
}

long alloc_quanta(usymlink_t ucon, usymlink_t thread, size_t amount)
{
        while (amount--) {
                check(alloc_quantum(ucon, thread));
        }
        return 0;
}

tag_t alloc_tag()
{
        size_t i;
        tag_t st;
        for (i = 0; i < LABEL_NR_TAGS; i++) {
                if (sys_alloc_tag(i, &st) == 0) {
                        return st;
                }
        }
        panic("Tag allocation failed");
}

long alloc_thread(usymlink_t *thread, usymlink_t ucon, struct label *secrecy, struct label *integrity, struct label *ownership, usymlink_t gate, const char *name)
{
        usymlink_t slabel, ilabel, olabel, tls;
        check(reserve_page(thread, ucon));
        check(reserve_page(&slabel, ucon));
        check(reserve_page(&ilabel, ucon));
        check(reserve_page(&olabel, ucon));
        check(alloc_block(&tls, ucon, secrecy, integrity, name));

        check(sys_alloc_thread(ucon.upage, thread->uparent_slot, slabel.uparent_slot, ilabel.uparent_slot, olabel.uparent_slot,
                               secrecy->tags, integrity->tags, ownership->tags, tls.uparent_slot, gate));

        if (name) page_set_name(*thread, name);

        return 0;
}

/* gate */
long alloc_gate(usymlink_t *ugte, usymlink_t ucon, struct label *secrecy, struct label *integrity, struct label *ownership, struct label *guard,
                usymlink_t pud, void *entry, uint64_t arg0, uint64_t arg1, uint64_t arg2, const char *name)
{
        usymlink_t slabel, ilabel, olabel, glabel;

        check(reserve_page(ugte, ucon));
        check(reserve_page(&slabel, ucon));
        check(reserve_page(&ilabel, ucon));
        check(reserve_page(&olabel, ucon));
        check(reserve_page(&glabel, ucon));

        check(sys_alloc_gate(ucon.upage, ugte->uparent_slot, slabel.uparent_slot, ilabel.uparent_slot, olabel.uparent_slot, glabel.uparent_slot,
              secrecy->tags, integrity->tags, ownership->tags, guard->tags, pud, entry, arg0, arg1, arg2));

        if (name) page_set_name(*ugte, name);

        return 0;
}

long gate_enter(usymlink_t ugte, struct label *ownership, uintptr_t arg, uintptr_t rsp)
{
        return sys_gate_enter(ugte.uparent, ugte.uparent_slot, ownership->tags, arg, rsp);
}

long gate_get_label(usymlink_t usym, struct label *secrecy, struct label *integrity, struct label *ownership)
{
        struct label osecrecy, ointegrity, oownership;
        if (!secrecy)
                secrecy = &osecrecy;
        if (!integrity)
                integrity = &ointegrity;
        if (!ownership)
                ownership = &oownership;

        ASSERT_MSG(usym.uparent_slot < CONTAINER_NR_PAGES, "gate_get_label");
        return sys_gate_get_label(usym.uparent, usym.uparent_slot, secrecy->tags, integrity->tags, ownership->tags);
}


long gate_call(usymlink_t ugte, usymlink_t alloc_container, uintptr_t arg)
{
        long r;
        extern long __nistar_sys_gate_call_ret;

        tag_t g;
        usymlink_t pud = USYMLINK_INVALID;
        usymlink_t return_gate;
        struct label secrecy, integrity, ownership, guard;
        label_init(&guard);
        g = alloc_tag();
        self_get_label(&secrecy, &integrity, &ownership);
        pud = self_get_pud();
        label_add_tag(&guard, g);

        alloc_gate(&return_gate, alloc_container, &secrecy, &integrity,
                   &ownership, &guard, pud, &__nistar_sys_gate_call_ret, 0, 0, 0, "ret");

        struct label g_ownership;
        gate_get_label(ugte, NULL, NULL, &g_ownership);

        label_union(&ownership, &g_ownership);

        r = sys_gate_call(ugte.uparent, ugte.uparent_slot, ownership.tags, arg,
                          return_gate.uparent, return_gate.uparent_slot, ownership.tags);

        label_remove_tag(&ownership, g);
        self_set_label(&secrecy, &integrity, &ownership);

        free_gate(return_gate);

        return r;
}

long alloc_call_gate(usymlink_t *ugte, usymlink_t ucont, struct label *secrecy, struct label *integrity,
                     struct label *ownership, struct label *guard, usymlink_t pud, void *entry, uint64_t arg1, const char *name)
{
        extern void _gate_entry();
        return alloc_gate(ugte, ucont, secrecy, integrity, ownership, guard, pud, _gate_entry, (uint64_t)entry, arg1, 0, name);
}


long alloc_container(usymlink_t *ucont, usymlink_t parent, struct label *secrecy, struct label *integrity, char *name)
{
        usymlink_t secrecyp, integrityp;

        check(reserve_page(ucont, parent));
        check(reserve_page(&secrecyp, parent));
        check(reserve_page(&integrityp, parent));

        check(sys_alloc_container(parent.upage, ucont->uparent_slot,
                                  secrecyp.uparent_slot, integrityp.uparent_slot,
                                  secrecy->tags, integrity->tags));

        if (name) page_set_name(*ucont, name);
        return 0;
}

long alloc_directory_pud(usymlink_t *pud, usymlink_t ucont, struct label *secrecy, struct label *integrity, char *name)
{
        usymlink_t secrecyp, integrityp;

        check(reserve_page(pud, ucont));
        check(reserve_page(&secrecyp, ucont));
        check(reserve_page(&integrityp, ucont));

        check(sys_alloc_directory_pud(ucont.upage, pud->uparent_slot, secrecyp.uparent_slot,
                                      integrityp.uparent_slot, secrecy->tags, integrity->tags));

        if (name) page_set_name(*pud, name);
        return 0;
}

long alloc_directory_pmd(usymlink_t *pmd, usymlink_t ucont, struct label *secrecy, struct label *integrity, char *name)
{
        usymlink_t secrecyp, integrityp;

        check(reserve_page(pmd, ucont));
        check(reserve_page(&secrecyp, ucont));
        check(reserve_page(&integrityp, ucont));

        check(sys_alloc_directory_pmd(ucont.upage, pmd->uparent_slot, secrecyp.uparent_slot,
                                      integrityp.uparent_slot, secrecy->tags, integrity->tags));

        if (name) page_set_name(*pmd, name);
        return 0;
}

long alloc_block(usymlink_t *blk, usymlink_t ucont, struct label *secrecy, struct label *integrity, const char *name)
{
        usymlink_t secrecyp, integrityp;

        check(reserve_page(blk, ucont));
        check(reserve_page(&secrecyp, ucont));
        check(reserve_page(&integrityp, ucont));

        check(sys_alloc_block(ucont.upage, blk->uparent_slot, secrecyp.uparent_slot,
                              integrityp.uparent_slot, secrecy->tags, integrity->tags));

        if (name) page_set_name(*blk, name);
        return 0;
}

long directory_get_slot(usymlink_t upud, size_t idx, usymlink_t *usym)
{
        long r;
        usymlink_t stack_sym;
        r = sys_directory_get_slot(upud.upage, idx, &stack_sym);
        if (r == 0) {
                r = container_find_slot(&stack_sym);
                if (r == 0 && usym != NULL)
                        *usym = stack_sym;
        }
        return r;
}

long directory_link_pmd(usymlink_t upud, size_t idx, usymlink_t upmd)
{
        return sys_directory_link_pmd(upud.upage, idx, upmd.uparent, upmd.uparent_slot);
}

long directory_link_block(usymlink_t upmd, size_t idx, usymlink_t block, pteval_t perm)
{
        return sys_directory_link_block(upmd.upage, idx, block.uparent, block.uparent_slot, perm);
}

long directory_unlink_pmd(usymlink_t upud, size_t idx)
{
        return sys_directory_unlink_pmd(upud.upage, idx);
}

long directory_unlink_block(usymlink_t upmd, size_t idx)
{
        return sys_directory_unlink_block(upmd.upage, idx);
}

/* free */

long free_page(usymlink_t usym)
{
        uint64_t type;
        long r;
        r = page_get_type(usym, &type);
        if (r < 0)
                return r;
        switch (type) {
                case PAGE_TYPE_GATE:
                        return free_gate(usym);
                case PAGE_TYPE_BLOCK:
                        return free_block(usym);
                case PAGE_TYPE_PUD:
                        return free_directory_pud(usym);
                case PAGE_TYPE_PMD:
                        return free_directory_pmd(usym);
                case PAGE_TYPE_THREAD:
                        return free_thread(usym);
        }
        ASSERT_MSG(false, "unhandled");
}

long free_page_recursive(usymlink_t usym)
{
        usymlink_t obj, parent;
        size_t slot;
        uint64_t type;
        uint64_t quota;
        long r;
        r = page_get_type(usym, &type);
        if (r < 0)
                return r;
        if (type != PAGE_TYPE_CONTAINER)
                return free_page(usym);
        for (slot = 0; slot < CONTAINER_NR_PAGES; slot++) {
                if (container_get_slot(usym, slot, &obj) == 0) {
                        r = free_page_recursive(obj);
                        if (r < 0)
                                return r;
                }
        }
        r = container_get_quota(usym, &quota);
        ASSERT_MSG(r == 0, "container_get_quota");
        r = page_get_container(usym, &parent);
        ASSERT_MSG(r == 0, "container_get_container");
        container_move_quota(usym, parent, quota);

        r = container_get_uquota(usym, &quota);
        ASSERT_MSG(r == 0, "container_get_uquota");
        container_move_uquota(usym, parent, quota);

        r = container_get_qquota(usym, &quota);
        ASSERT_MSG(r == 0, "container_get_qquota");
        container_move_qquota(usym, parent, quota);
        alloc_quanta(parent, self_get(), quota);

        free_container(usym);

        return 0;
}

long free_gate(usymlink_t usym)
{
        return sys_free_gate(usym.uparent, usym.uparent_slot);
}

long free_block(usymlink_t usym)
{
        return sys_free_block(usym.uparent, usym.uparent_slot);
}

long free_directory_pud(usymlink_t usym)
{
        return sys_free_directory_pud(usym.uparent, usym.uparent_slot);
}

long free_directory_pmd(usymlink_t usym)
{
        return sys_free_directory_pmd(usym.uparent, usym.uparent_slot);
}

long free_thread(usymlink_t usym)
{
        return sys_free_thread(usym.uparent, usym.uparent_slot);
}

long free_container(usymlink_t usym)
{
        return sys_free_container(usym.uparent, usym.uparent_slot);
}

long net_transmit(const void *ptr, size_t len)
{
        long r;
        uint64_t written;
        uint64_t buf[512];

        ASSERT_MSG(len <= sizeof(buf), "too big transmit");

        memcpy((char *) buf, ptr, len);

        r = sys_net_transmit((char *) buf, len, &written);
        ASSERT_MSG(r == 0, "sys_net_transmit");

        return written;
}

long net_receive(void *ptr, size_t len)
{
        long r;
        uint64_t read;
        uint64_t buf[512];

        ASSERT_MSG(len <= sizeof(buf), "too big receive");

        r = sys_net_receive((char *) buf, len, &read);
        ASSERT_MSG(r == 0, "sys_net_receive");

        memcpy((char *) ptr, buf, len);

        return read;
}

/* debugging */

static noreturn void die(void)
{
        /* init: stay here for debugging */
        while (1)
                ;
        __builtin_unreachable();
}

static void error_callback(void *data, const char *msg, int errnum)
{
        debug_printf("libbacktrace: %s\n", msg);
}

static int print_callback(void *data, uintptr_t pc,
                          const char *filename, int lineno,
                          const char *function)
{
        debug_printf("0x%lx %s\n\t%s:%d\n",
                     (unsigned long)pc,
                     (!function) ? "???" : function,
                     (!filename) ? "???" : filename,
                     lineno);
        return 0;
}

static void backtrace(void)
{
        struct stat st;
        uint64_t *fp;
        struct backtrace_state *state;

        if (lstat(program_invocation_name, &st) < 0) {
                debug_printf("Could not open file: %s\n", program_invocation_name);
                for (fp = __builtin_frame_address(0); fp; fp = (uint64_t *)fp[0]) {
                        debug_printf("[<%016lx>]\n", fp[1]);
                }
        } else {
                state = backtrace_create_state(program_invocation_name, 0, error_callback, NULL);
                backtrace_full(state, 0, print_callback, error_callback, NULL);
        }
}

noreturn void panic(const char *fmt, ...)
{
        char buf[1024];

        debug_printf("PANIC: ");
        va_list ap;
        va_start(ap, fmt);
        vsprintf(buf, fmt, ap);
        va_end(ap);
        sys_debug_print(buf);
        debug_printf("\n");

        backtrace();
        die();
}

void debug_printf(const char *fmt, ...)
{
        char buf[1024];
        va_list ap;
        va_start(ap, fmt);
        vsprintf(buf, fmt, ap);
        va_end(ap);
        sys_debug_print(buf);
}

static const char *typenames[] = {
        [PAGE_TYPE_NONE]      = "NONE",
        [PAGE_TYPE_UNTYPED]   = "UNTYPED",
        [PAGE_TYPE_LABEL]     = "LABEL",
        [PAGE_TYPE_CONTAINER] = "CONTAINER",
        [PAGE_TYPE_PGD]       = "PGD",
        [PAGE_TYPE_PUD]       = "PUD",
        [PAGE_TYPE_PMD]       = "PMD",
        [PAGE_TYPE_GATE]      = "GATE",
        [PAGE_TYPE_THREAD]    = "THREAD",
        [PAGE_TYPE_BLOCK]     = "BLOCK",
};

static const char *threadstate[] = {
        [THREAD_STATE_NONE]       = "NONE",
        [THREAD_STATE_RUNNABLE]   = "RUNNABLE",
        [THREAD_STATE_HALTED]     = "HALTED",
};


static void _debug_print_directory(usymlink_t ucon, char *indent, bool recurse)
{
        size_t i;
        char name[PAGE_NAME_LEN];
        char secrecybuf[256];
        char integritybuf[256];
        usymlink_t usym;
        uint64_t type, quota, uquota;
        struct label secrecy, integrity;
        label_init(&secrecy);
        label_init(&integrity);

        for(i = 0; i < DIRECTORY_NR_ENTRIES; i++) {
                if (directory_get_slot(ucon, i, &usym) == 0) {
                        ASSERT_MSG(page_get_type(usym, &type) == 0, "Could not get page type\n");
                        if (page_get_name(usym, name) != 0)
                                strlcpy(name, "???", sizeof(name));
                        if (page_get_label(usym, &secrecy, &integrity) == 0) {
                                label_format(&secrecy, secrecybuf, sizeof(secrecybuf));
                                label_format(&integrity, integritybuf, sizeof(integritybuf));
                        } else {
                                strcpy(secrecybuf, "???");
                                strcpy(integritybuf, "???");
                        }

                        debug_printf("%s%03zu %-16s %-9s %016lx %016lx %s %s", indent, i, name, typenames[type], (uint64_t)(usym.upage >> 64), (uint64_t)usym.upage, secrecybuf, integritybuf);
                        switch (type)
                        {
                                case PAGE_TYPE_CONTAINER:
                                        check(container_get_quota(usym, &quota));
                                        check(container_get_uquota(usym, &uquota));
                                        debug_printf(" %3lu %3lu", quota, uquota);
                                        break;
                        }

                        debug_printf("\n");

                        if (recurse && (type == PAGE_TYPE_PUD || type == PAGE_TYPE_PMD)) {
                                strcat(indent, "  ");
                                _debug_print_directory(usym, indent, recurse);
                                indent[strlen(indent)-2] = 0;
                        }

                }

        }
}

static void _debug_print_container(usymlink_t ucon, char *indent, bool recurse)
{
        long r, tstate;
        size_t i;
        char name[PAGE_NAME_LEN];
        char secrecybuf[256];
        char integritybuf[256];
        usymlink_t usym;
        uint64_t type, quota, uquota, qquota;
        struct label secrecy, integrity;
        label_init(&secrecy);
        label_init(&integrity);

        for(i = 0; i < CONTAINER_NR_PAGES; i++) {
                if (container_get_slot(ucon, i, &usym) == 0) {
                        ASSERT_MSG(page_get_type(usym, &type) == 0, "Could not get page type\n");
                        if (page_get_name(usym, name) != 0)
                                strlcpy(name, "???", sizeof(name));
                        if (page_get_label(usym, &secrecy, &integrity) == 0) {
                                label_format(&secrecy, secrecybuf, sizeof(secrecybuf));
                                label_format(&integrity, integritybuf, sizeof(integritybuf));
                        } else {
                                strcpy(secrecybuf, "???");
                                strcpy(integritybuf, "???");
                        }

                        debug_printf("%s%03zu %-32s %-9s %016lx %016lx %s %s", indent, i, name, typenames[type], (uint64_t)(usym.upage >> 64), (uint64_t)usym.upage, secrecybuf, integritybuf);
                        switch (type)
                        {
                                case PAGE_TYPE_CONTAINER:
                                        r = container_get_quota(usym, &quota);
                                        if (r == 0) {
                                                check(container_get_uquota(usym, &uquota));
                                                check(container_get_qquota(usym, &qquota));
                                                debug_printf(" %3lu %3lu %3lu", quota, uquota, qquota);
                                        } else {
                                                debug_printf(" ??? ??? ???");
                                        }
                                        break;
                                case PAGE_TYPE_THREAD:
                                        tstate = thread_get_state(usym);
                                        ASSERT_MSG(tstate <= THREAD_STATE_HALTED, "Invalid thread state\n");
                                        debug_printf(" %s", threadstate[tstate]);
                        }

                        debug_printf("\n");

                        if (recurse && type == PAGE_TYPE_CONTAINER) {
                                strcat(indent, "  ");
                                _debug_print_container(usym, indent, recurse);
                                indent[strlen(indent)-2] = 0;
                        }

                        if (recurse && (type == PAGE_TYPE_PUD || type == PAGE_TYPE_PMD)) {
                                strcat(indent, "  ");
                                _debug_print_directory(usym, indent, recurse);
                                indent[strlen(indent)-2] = 0;
                        }

                }

        }
}

void debug_print_label(struct label *la)
{
        char buf[1024];
        label_format(la, buf, sizeof(buf));
        debug_printf("%s\n", buf);
}

void debug_print_container(usymlink_t ucon)
{
        _debug_print_container(ucon, "", false);
}

void debug_print_directory(usymlink_t dir)
{
        _debug_print_directory(dir, "", false);
}

void debug_print_directory_recursive(usymlink_t udir)
{
        char indent[128];
        memset(indent, 0, sizeof(indent));
        _debug_print_directory(udir, indent, true);
}

void debug_print_container_recursive(usymlink_t ucon)
{
        char indent[128];
        memset(indent, 0, sizeof(indent));
        _debug_print_container(ucon, indent, true);
}

void debug_print_usym(usymlink_t ucon)
{
        debug_printf("usym: %016lx %016lx -- %016lx %016lx\n", (uint64_t)(ucon.upage >> 64), (uint64_t)ucon.upage,
                                                               (uint64_t)(ucon.uparent >> 64), (uint64_t)(ucon.uparent));
}
