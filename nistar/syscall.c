#include <asm/ptrace.h>
#include <asm/setup.h>
#include <asm/tsc.h>
#include <crypto/aes.h>
#include <crypto/random.h>
#include <sys/console.h>
#include <sys/errno.h>
#include <sys/percpu.h>
#include <sys/safe.h>
#include <sys/string.h>
#include <uapi/nistar/memlayout.h>

#include "traps.h"
#include "mm.h"
#include "block.h"
#include "container.h"
#include "directory.h"
#include "gate.h"
#include "label.h"
#include "sched.h"
#include "thread.h"

enum {
#define __SYSCALL(x) SYS_##x,
#include <uapi/nistar/syscall.inc>
#undef __SYSCALL
};

struct sys_extra_args {
        size_t extra0;
        size_t extra1;
        size_t extra2;
        size_t extra3;
        size_t extra4;
        size_t extra5;
        size_t extra6;
        size_t extra7;
        size_t extra8;
        size_t extra9;
        size_t extra10;
};

static struct crypto_aes_ctx aes128_ctx;


#define TLS_NR_SLOTS            (PAGE2M_SIZE / sizeof(uint64_t))

/* n should be constant */
static inline bool tls_is_valid(size_t i, size_t n)
{
        return i <= TLS_NR_SLOTS - n;
}

static uint64_t *tls_entries(void)
{
        struct thread *thread;

        thread = page_data(get_current_thread());
        return block_data(thread->local);
}

noinline long _copy_from_user(void *to, size_t from, size_t n)
{
        memcpy(to, tls_entries() + from, n * sizeof(uint64_t));
        return 0;
}

noinline long _copy_to_user(size_t to, const void *from, size_t n)
{
        memcpy(tls_entries() + to, from, n * sizeof(uint64_t));
        return 0;
}

long copy_from_user(void *to, size_t from, size_t n)
{
        if (!tls_is_valid(from, n))
                return -EINVAL;
        return _copy_from_user(to, from, n);
}

long copy_to_user(size_t to, const void *from, size_t n)
{
        if (!tls_is_valid(to, n))
                return -EINVAL;
        return _copy_to_user(to, from, n);
}

noinline static void kpage_to_upage(kpage_id_t *ksym, upage_id_t *usym)
{
        memcpy(usym, ksym, 16);
        /* aes_encrypt(&aes128_ctx, usym, ksym); */
}

noinline static void upage_to_kpage(upage_id_t *usym, kpage_id_t *ksym)
{
        memcpy(ksym, usym, 16);
        /* aes_decrypt(&aes128_ctx, ksym, usym); */
}

static void ksymlink_to_usymlink(ksymlink_t *ksym, usymlink_t *usym)
{
        kpage_to_upage(&ksym->page, &usym->upage);
        kpage_to_upage(&ksym->parent, &usym->uparent);
}

static void usymlink_to_ksymlink(usymlink_t *usym, ksymlink_t *ksym)
{
        upage_to_kpage(&usym->upage, &ksym->page);
        upage_to_kpage(&usym->uparent, &ksym->parent);
}

static long untyped_to_type(page_id_t id, uint64_t type)
{
        switch (type) {
        case PAGE_TYPE_CONTAINER:
                return untyped_to_container(id);
        case PAGE_TYPE_PUD:
        case PAGE_TYPE_PMD:
                return untyped_to_directory(id, type);
        case PAGE_TYPE_GATE:
                return untyped_to_gate(id);
        case PAGE_TYPE_THREAD:
                return untyped_to_thread(id);
        }

        BUG_ON(true);
}

static long alloc_labels(page_id_t secrecy, page_id_t integrity, struct label *requested_secrecy, struct label *requested_integrity)
{
        int r;
        page_id_t tid;
        struct thread *thread;
        struct label *thread_secrecy, *thread_integrity, *thread_ownership;

        if (safe_equal(page_id, secrecy, integrity))
                return -EINVAL;
        if (!page_is_type(secrecy, PAGE_TYPE_UNTYPED))
                return -EINVAL;
        if (!page_is_type(integrity, PAGE_TYPE_UNTYPED))
                return -EINVAL;

        tid = get_current_thread();
        thread = page_data(tid);
        thread_secrecy = get_label(page_get(tid)->secrecy);
        thread_integrity = get_label(page_get(tid)->integrity);
        thread_ownership = get_label(thread->ownership);

        // Check if current thread can allocate these labels
        if (!label_is_subsetx(thread_secrecy, requested_secrecy, thread_ownership))
                return -EACCES;
        if (!label_is_subsetx(requested_integrity, thread_integrity, thread_ownership))
                return -EACCES;
        r = untyped_to_label(secrecy);
        if (r)
                return r;
        r = untyped_to_label(integrity);
        if (r)
                return r;

        set_label(secrecy, requested_secrecy);
        set_label(integrity, requested_integrity);

        return 0;
}

static long alloc_page(upage_id_t ucon, size_t cslot, size_t sslot, size_t islot, struct label *secrecy, struct label *integrity, uint64_t type)
{
        int r;
        kpage_id_t kcon;
        struct container *container;

        if (!(cslot < CONTAINER_NR_PAGES))
                return -EINVAL;
        if (!(sslot < CONTAINER_NR_PAGES))
                return -EINVAL;
        if (!(islot < CONTAINER_NR_PAGES))
                return -EINVAL;
        if (cslot == sslot || cslot == islot || sslot == islot)
                return -EINVAL;
        upage_to_kpage(&ucon, &kcon);
        if (!kpage_is_type(kcon, PAGE_TYPE_CONTAINER))
                return -EINVAL;
        if (!thread_can_read_write_page(get_current_thread(), kcon.id))
                return -EACCES;
        container = page_data(kcon.id);
        if (!page_is_type(container->pages[cslot], PAGE_TYPE_UNTYPED))
                return -EINVAL;
        r = alloc_labels(container->pages[sslot], container->pages[islot], secrecy, integrity);
        if (r)
                return r;
        r = untyped_to_type(container->pages[cslot], type);
        if (r)
                return r;

        /* TODO: This should be set by reserve page to ensure uniqueness of each container value */
        page_get(container->pages[cslot])->c_parent = kcon.id;
        page_get(container->pages[cslot])->c_parent_slot = cslot;

        page_get(container->pages[cslot])->secrecy = container->pages[sslot];
        page_get(container->pages[cslot])->integrity = container->pages[islot];
        container->pages[sslot] = PAGE_ID_INVALID;
        container->pages[islot] = PAGE_ID_INVALID;
        return 0;
}

static long container_free_page(page_id_t cid, page_id_t id, uint64_t type)
{
        long r;

        switch (type) {
                case PAGE_TYPE_GATE:
                        r = gate_free(cid, id);
                        break;
                case PAGE_TYPE_BLOCK:
                        r = block_free(cid, id);
                        /* TODO: more efficient dealloc of blocks */
                        cpu_invalidate_pgtable();
                        return 0;
                case PAGE_TYPE_PUD:
                case PAGE_TYPE_PMD:
                        r = directory_free(cid, id);
                        /* TODO: more efficient dealloc AS */
                        cpu_invalidate_pgtable();
                        break;
                case PAGE_TYPE_THREAD:
                        r = thread_free(cid, id);
                        break;
                case PAGE_TYPE_CONTAINER:
                        r = container_free(cid, id);
                        break;
        }

        return r;
}

static long free_page(upage_id_t ucon, size_t slot, uint64_t type)
{
        long r;
        kpage_id_t kcon;
        page_id_t id;
        struct container *container;
        if (!(slot < CONTAINER_NR_PAGES))
                return -EINVAL;
        upage_to_kpage(&ucon, &kcon);
        if (!kpage_is_type(kcon, PAGE_TYPE_CONTAINER))
                return -EINVAL;
        if (!thread_can_read_write_page(get_current_thread(), kcon.id))
                return -EACCES;
        container = page_data(kcon.id);
        id = container->pages[slot];
        if (!page_is_type(id, type))
                return -EINVAL;
        if (!thread_can_read_write_page(get_current_thread(), id))
                return -EACCES;
        r = container_free_page(kcon.id, id, type);
        if (r < 0)
                return r;
        container->pages[slot] = PAGE_ID_INVALID;
        return 0;
}

static void thread_set_gate(struct thread *thread, struct gate *gate)
{
        thread->mm = gate->mm;
        thread->cpu.rip = gate->entry;
        thread->cpu.rdi = gate->args[0];
        thread->cpu.rsi = gate->args[1];
        thread->cpu.rdx = gate->args[2];
        thread->cpu.rcx = gate->args[3];
        thread->cpu.r8 = gate->args[4];
        thread->cpu.r9 = gate->args[5];
        BUILD_BUG_ON(GATE_NR_ARGS != 6);
}

static long sys_container_get_root(size_t to)
{
        kpage_id_t ksym;
        upage_id_t usym;

        ksym = __kpage_id(root_container_id);
        kpage_to_upage(&ksym, &usym);
        return copy_to_user(to, &usym, sizeof(kpage_id_t) / sizeof(uint64_t));
}

long sys_container_get_root64(size_t to)
{
        return copy_to_user(to, &root_container_id, 1);
}


static long sys_container_get_slot(upage_id_t ucon, size_t slot, size_t to)
{
        struct container *container;
        kpage_id_t kcon;
        kpage_id_t kobj;
        upage_id_t uobj;

        if (!(slot < CONTAINER_NR_PAGES))
                return -EINVAL;
        upage_to_kpage(&ucon, &kcon);
        if (!kpage_is_type(kcon, PAGE_TYPE_CONTAINER))
                return -EACCES;
        if (!thread_can_read_page(get_current_thread(), kcon.id))
                return -EACCES;
        container = page_data(kcon.id);
        if (!page_is_valid(container->pages[slot]))
                return -EINVAL;

        kobj = __kpage_id(container->pages[slot]);
        kpage_to_upage(&kobj, &uobj);
        return copy_to_user(to, &uobj, sizeof(kpage_id_t) / sizeof(uint64_t));
}

long sys_container_get_slot64(page_id_t con, size_t slot, size_t to)
{
        struct container *container;

        if (!(slot < CONTAINER_NR_PAGES))
                return -EINVAL;
        if (!page_is_type(con, PAGE_TYPE_CONTAINER))
                return -EACCES;
        if (!thread_can_read_page(get_current_thread(), con))
                return -EACCES;
        container = page_data(con);
        if (!page_is_valid(container->pages[slot]))
                return -EINVAL;
        return copy_to_user(to, &container->pages[slot], 1);
}

static long sys_container_get_quota(upage_id_t ucon, size_t to)
{
        kpage_id_t kcon;
        upage_to_kpage(&ucon, &kcon);
        if (!kpage_is_type(kcon, PAGE_TYPE_CONTAINER))
                return -EACCES;
        if (!thread_can_read_page(get_current_thread(), kcon.id))
                return -EACCES;

        return copy_to_user(to, &page_get(kcon.id)->c_quota, 1);
}

static long sys_container_get_uquota(upage_id_t ucon, size_t to)
{
        kpage_id_t kcon;
        upage_to_kpage(&ucon, &kcon);
        if (!kpage_is_type(kcon, PAGE_TYPE_CONTAINER))
                return -EACCES;
        if (!thread_can_read_page(get_current_thread(), kcon.id))
                return -EACCES;

        return copy_to_user(to, &page_get(kcon.id)->c_uquota, 1);
}

static long sys_container_get_qquota(upage_id_t ucon, size_t to)
{
        kpage_id_t kcon;
        upage_to_kpage(&ucon, &kcon);
        if (!kpage_is_type(kcon, PAGE_TYPE_CONTAINER))
                return -EACCES;
        if (!thread_can_read_page(get_current_thread(), kcon.id))
                return -EACCES;

        return copy_to_user(to, &page_get(kcon.id)->c_qquota, 1);
}

static long sys_container_move_quota(upage_id_t from, upage_id_t to)
{
        kpage_id_t kfrom, kto;
        struct page *pfrom;

        upage_to_kpage(&from, &kfrom);
        if (!kpage_is_type(kfrom, PAGE_TYPE_CONTAINER))
                return -EINVAL;
        if (!thread_can_read_write_page(get_current_thread(), kfrom.id))
                return -EACCES;
        upage_to_kpage(&to, &kto);
        if (!kpage_is_type(kto, PAGE_TYPE_CONTAINER))
                return -EINVAL;
        if (!thread_can_read_write_page(get_current_thread(), kto.id))
                return -EACCES;
        pfrom = page_get(kfrom.id);
        if (pfrom->c_quota == 0)
                return -ENOMEM;
        container_push(kto.id, container_pop(kfrom.id));
        return 0;
}

static long sys_container_move_uquota(upage_id_t from, upage_id_t to)
{
        kpage_id_t kfrom, kto;
        struct page *pfrom;

        upage_to_kpage(&from, &kfrom);
        if (!kpage_is_type(kfrom, PAGE_TYPE_CONTAINER))
                return -EINVAL;
        if (!thread_can_read_write_page(get_current_thread(), kfrom.id))
                return -EACCES;
        upage_to_kpage(&to, &kto);
        if (!kpage_is_type(kto, PAGE_TYPE_CONTAINER))
                return -EINVAL;
        if (!thread_can_read_write_page(get_current_thread(), kto.id))
                return -EACCES;
        pfrom = page_get(kfrom.id);
        if (pfrom->c_uquota == 0)
                return -ENOMEM;
        container_push_page2m(kto.id, container_pop_page2m(kfrom.id));
        return 0;
}

static long sys_container_move_qquota(upage_id_t from, quantum_id_t qid, upage_id_t to)
{
        kpage_id_t kfrom, kto;
        struct quantum *q;
        struct page *pfrom, *pto;

        if (!quantum_is_valid(qid))
                return -EINVAL;
        upage_to_kpage(&from, &kfrom);
        if (!kpage_is_type(kfrom, PAGE_TYPE_CONTAINER))
                return -EACCES;
        if (!thread_can_read_write_page(get_current_thread(), kfrom.id))
                return -EACCES;
        pfrom = page_get(kfrom.id);
        if (pfrom->c_qquota == 0)
                return -EDQUOT;
        q = quantum_get(qid);
        if (!safe_equal(page_id, q->container, kfrom.id))
                return -ENOENT;
        upage_to_kpage(&to, &kto);
        if (!kpage_is_type(kto, PAGE_TYPE_CONTAINER))
                return -EACCES;
        if (!thread_can_read_write_page(get_current_thread(), kto.id))
               return -EACCES;
        pto = page_get(kto.id);

        pfrom->c_qquota -= 1;
        pto->c_qquota += 1;
        q->container = kto.id;

        return 0;
}

static long sys_container_get_parent(upage_id_t ucon, size_t to)
{
        kpage_id_t kcon, ksym;
        upage_id_t usym;
        upage_to_kpage(&ucon, &kcon);
        if (!kpage_is_type(kcon, PAGE_TYPE_CONTAINER))
                return -EINVAL;
        if (!thread_can_read_page(get_current_thread(), kcon.id))
                return -EACCES;

        ksym = __kpage_id(page_get(kcon.id)->c_parent);
        kpage_to_upage(&ksym, &usym);
        return copy_to_user(to, &usym, sizeof(kpage_id_t) / sizeof(uint64_t));
}

static long sys_reserve_page(upage_id_t ucon, size_t slot)
{
        kpage_id_t kcon;
        upage_to_kpage(&ucon, &kcon);
        if (!kpage_is_type(kcon, PAGE_TYPE_CONTAINER))
                return -EINVAL;
        if (!thread_can_read_write_page(get_current_thread(), kcon.id))
                return -EACCES;
        return container_reserve_page(kcon.id, slot);
}

static long sys_alloc_quantum(upage_id_t ucon, quantum_id_t qid, upage_id_t uthread)
{
        page_id_t tid;
        kpage_id_t kcon, kthread;
        upage_to_kpage(&ucon, &kcon);
        upage_to_kpage(&uthread, &kthread);
        struct quantum *q;
        if (!page_is_valid(kthread.id))
                return -EINVAL;
        if (!quantum_is_valid(qid))
                return -EINVAL;
        if (!kpage_is_type(kcon, PAGE_TYPE_CONTAINER))
                return -EACCES;
        if (!thread_can_read_write_page(get_current_thread(), kcon.id))
                return -EACCES;
        if (page_get(kcon.id)->c_qquota == 0)
                return -EDQUOT;
        q = quantum_get(qid);
        if (!safe_equal(page_id, q->container, kcon.id))
                return -ENOENT;

        q->thread = kthread.id;
        tid = get_current_thread();

        /* The currently running process might have changed. */
        if (!safe_equal(page_id, tid, sched_get_current()))
            sched_run(sched_get_current());

        return 0;
}

static long sys_alloc_tag(size_t slot, size_t to)
{
        struct page *page;
        struct thread *thread;
        struct label *ownership;

        if (!(slot < LABEL_NR_TAGS))
                return -EINVAL;

        page = page_get(get_current_thread());
        thread = page_data(get_current_thread());
        ownership = get_label(thread->ownership);

        if (page->tag_counter == UINT64_MAX)
                return -EOVERFLOW;
        if (tag_is_valid(ownership->tags[slot]))
                return -EINVAL;
        if (!tls_is_valid(to, sizeof(tag_t) / sizeof(uint64_t)))
                return -EINVAL;

        tag_t t = tag_alloc();
        ownership->tags[slot] = t;
        return _copy_to_user(to, &t, sizeof(tag_t) / sizeof(uint64_t));
}

long do_alloc_container(upage_id_t ucon, size_t slot, size_t sslot, size_t islot, struct label *secrecy, struct label *integrity)
{
        return alloc_page(ucon, slot, sslot, islot, secrecy, integrity, PAGE_TYPE_CONTAINER);
}

static long sys_alloc_container(upage_id_t ucon, size_t slot, size_t sslot, size_t islot, size_t rest)
{
        int r;
        struct sys_extra_args args;
        struct label secrecy;
        struct label integrity;

        r = copy_from_user(&args, rest, 2);
        if (r)
                return r;
        r = copy_from_user(secrecy.tags, args.extra0, sizeof(secrecy.tags) / sizeof(uint64_t));
        if (r)
                return r;
        r = copy_from_user(integrity.tags, args.extra1, sizeof(integrity.tags) / sizeof(uint64_t));
        if (r)
                return r;

        return do_alloc_container(ucon, slot, sslot, islot, &secrecy, &integrity);
}

long do_alloc_block(upage_id_t ucon, size_t slot, size_t sslot, size_t islot, struct label *secrecy, struct label *integrity)
{
        long r;
        kpage_id_t kcon;
        struct page *cp;
        struct container *container;
        if (!(slot < CONTAINER_NR_PAGES))
                return -EINVAL;
        if (!(sslot < CONTAINER_NR_PAGES))
                return -EINVAL;
        if (!(islot < CONTAINER_NR_PAGES))
                return -EINVAL;
        if (slot == sslot || slot == islot || sslot == islot)
                return -EINVAL;
        upage_to_kpage(&ucon, &kcon);
        if (!kpage_is_type(kcon, PAGE_TYPE_CONTAINER))
                return -EINVAL;
        if (!thread_can_read_write_page(get_current_thread(), kcon.id))
                return -EACCES;
        cp = page_get(kcon.id);
        if (cp->c_uquota == 0)
                return -EDQUOT;
        container = page_data(kcon.id);
        if (!page_is_type(container->pages[slot], PAGE_TYPE_UNTYPED))
                return -EINVAL;
        r = alloc_labels(container->pages[sslot], container->pages[islot], secrecy, integrity);
        if (r)
                return r;
        r = untyped_to_block(container->pages[slot], container_pop_page2m(kcon.id));
        if (r)
                return r;
        page_get(container->pages[slot])->secrecy = container->pages[sslot];
        page_get(container->pages[slot])->integrity = container->pages[islot];
        container->pages[sslot] = PAGE_ID_INVALID;
        container->pages[islot] = PAGE_ID_INVALID;
        return 0;
}

static long sys_alloc_block(upage_id_t ucon, size_t slot, size_t sslot, size_t islot, size_t rest)
{
        long r;
        struct sys_extra_args args;
        struct label secrecy, integrity;

        r = copy_from_user(&args, rest, 2);
        if (r)
                return r;
        r = copy_from_user(secrecy.tags, args.extra0, sizeof(secrecy.tags) / sizeof(uint64_t));
        if (r)
                return r;
        r = copy_from_user(integrity.tags, args.extra1, sizeof(integrity.tags) / sizeof(uint64_t));
        if (r)
                return r;
        return do_alloc_block(ucon, slot, sslot, islot, &secrecy, &integrity);
}

long do_alloc_thread(upage_id_t ucon, size_t slot, size_t sslot, size_t islot,
                     size_t oslot, struct label *secrecy, struct label *integrity,
                     struct label *requested_ownership, size_t tslot,
                     upage_id_t ugate_page, upage_id_t ugate_parent_page)
{
        long r;
        struct label *thread_ownership;
        struct container *container;
        struct thread *thread;
        struct gate *gate;
        usymlink_t ugate;
        ksymlink_t kgate;
        kpage_id_t kcon;
        ugate.upage = ugate_page;
        ugate.uparent = ugate_parent_page;
        if (oslot == slot)
                return -EINVAL;
        if (oslot == sslot)
                return -EINVAL;
        if (oslot == islot)
                return -EINVAL;
        if (!(tslot < CONTAINER_NR_PAGES))
                return -EINVAL;
        if (!(oslot < CONTAINER_NR_PAGES))
                return -EINVAL;
        thread = get_thread(get_current_thread());
        thread_ownership = get_label(thread->ownership);
        /* requested ownership ⊆ current thread ownership */
        if (!label_is_subset(requested_ownership, thread_ownership))
                return -EACCES;
        upage_to_kpage(&ucon, &kcon);
        if (!kpage_is_type(kcon, PAGE_TYPE_CONTAINER))
                return -EINVAL;
        if (!thread_can_read_write_page(get_current_thread(), kcon.id))
                return -EACCES;
        container = page_data(kcon.id);
        /* TODO: a non-mappable TLS type..  */
        if (!page_is_type(container->pages[tslot], PAGE_TYPE_BLOCK))
                return -EINVAL;
        if (!page_is_type(container->pages[oslot], PAGE_TYPE_UNTYPED))
                return -EINVAL;
        usymlink_to_ksymlink(&ugate, &kgate);
        if (!ksymlink_is_type(kgate, PAGE_TYPE_GATE))
                return -EINVAL;
        if (!thread_can_read_page(get_current_thread(), kgate.page.id))
                return -EACCES;
        if (!thread_can_read_page(get_current_thread(), kgate.parent.id))
                return -EACCES;
        r = alloc_page(ucon, slot, sslot, islot, secrecy, integrity, PAGE_TYPE_THREAD);
        if (r)
                return r;
        r = untyped_to_label(container->pages[oslot]);
        if (r)
                return r;
        set_label(container->pages[oslot], requested_ownership);

        thread = get_thread(container->pages[slot]);
        thread->ownership = container->pages[oslot];
        thread_clear_tls(container->pages[slot]);
        thread->local = container->pages[tslot];

        gate = get_gate(kgate.page.id);
        thread_set_gate(thread, gate);
        thread->state = THREAD_STATE_RUNNABLE;
        thread->cpu.rsp = USER_STACK_TOP;
        thread->fsbase = USER_TLS_START;

        container->pages[oslot] = PAGE_ID_INVALID;
        container->pages[tslot] = PAGE_ID_INVALID;

        return 0;
}

static long sys_alloc_thread(upage_id_t ucon, size_t slot, size_t sslot, size_t islot, size_t rest)
{
        long r;
        struct sys_extra_args args;
        size_t oslot, tslot, usecrecy, uintegrity, uownership;
        struct label secrecy, integrity, ownership;
        usymlink_t ugate;

        r = copy_from_user(&args, rest, 6);
        if (r)
                return r;
        oslot = args.extra0;
        usecrecy = args.extra1;
        uintegrity = args.extra2;
        uownership = args.extra3;
        tslot = args.extra4;
        r = copy_from_user(secrecy.tags, usecrecy, sizeof(secrecy.tags) / sizeof(uint64_t));
        if (r)
                return r;
        r = copy_from_user(integrity.tags, uintegrity, sizeof(integrity.tags) / sizeof(uint64_t));
        if (r)
                return r;
        r = copy_from_user(ownership.tags, uownership, sizeof(ownership.tags) / sizeof(uint64_t));
        if (r)
                return r;
        r = copy_from_user(&ugate, args.extra5, sizeof(usymlink_t) / sizeof(uint64_t));
        if (r)
                return r;
        return do_alloc_thread(ucon, slot, sslot, islot, oslot,
                               &secrecy, &integrity, &ownership,
                               tslot, ugate.upage, ugate.uparent);
}

long do_alloc_gate(upage_id_t ucon, size_t slot, size_t sslot, size_t islot,
                   size_t oslot, size_t gslot, struct label *secrecy, struct label *integrity,
                   struct label *requested_ownership, struct label *guard,
                   upage_id_t upud_page, upage_id_t upud_parent_page, size_t entry,
                   uint64_t gatearg0, uint64_t gatearg1, uint64_t gatearg2)
{
        long r;
        ksymlink_t kpud;
        kpage_id_t kcon;
        struct thread *thread;
        struct label *thread_ownership;
        struct container *container;
        struct gate *gate;
        /* ownership is unique */
        if (oslot == gslot || oslot == slot || oslot == sslot || oslot == islot)
                return -EINVAL;
        /* oslot is a valid container index */
        if (!(oslot < CONTAINER_NR_PAGES))
                return -EINVAL;
        /* verify is unique */
        if (gslot == slot || gslot == sslot || gslot == islot)
                return -EINVAL;
        /* gslot is a valid container index */
        if (!(gslot < CONTAINER_NR_PAGES))
                return -EINVAL;
        /* read the pud sym */
        usymlink_t upud;
        upud.upage = upud_page;
        upud.uparent = upud_parent_page;
        thread = get_thread(get_current_thread());
        thread_ownership = get_label(thread->ownership);
        /* requested ownership ⊆ current thread ownership */
        if (!label_is_subset(requested_ownership, thread_ownership))
                return -EACCES;
        usymlink_to_ksymlink(&upud, &kpud);
        /* pud validation */
        if (!ksymlink_is_type(kpud, PAGE_TYPE_PUD))
                return -EINVAL;
        if (!thread_can_read_page(get_current_thread(), kpud.parent.id))
                return -EACCES;
        if (!thread_can_read_page(get_current_thread(), kpud.page.id))
                return -EACCES;
        upage_to_kpage(&ucon, &kcon);
        /* container validation */
        if (!kpage_is_type(kcon, PAGE_TYPE_CONTAINER))
                return -EINVAL;
        if (!thread_can_read_write_page(get_current_thread(), kcon.id))
                return -EACCES;
        container = page_data(kcon.id);
        /* ownership page must be free */
        if (!page_is_type(container->pages[oslot], PAGE_TYPE_UNTYPED))
                return -EINVAL;
        /* guard page must be free */
        if (!page_is_type(container->pages[gslot], PAGE_TYPE_UNTYPED))
                return -EINVAL;
        r = alloc_page(ucon, slot, sslot, islot, secrecy, integrity, PAGE_TYPE_GATE);
        if (r)
                return r;
        r = untyped_to_label(container->pages[oslot]);
        if (r)
                return r;
        r = untyped_to_label(container->pages[gslot]);
        if (r)
                return r;

        set_label(container->pages[oslot], requested_ownership);
        set_label(container->pages[gslot], guard);

        gate = get_gate(container->pages[slot]);
        gate->ownership = container->pages[oslot];
        gate->guard = container->pages[gslot];
        gate->mm = kpud;
        gate->entry = entry;
        gate->args[0] = gatearg0;
        gate->args[1] = gatearg1;
        gate->args[2] = gatearg2;
        container->pages[oslot] = PAGE_ID_INVALID;
        container->pages[gslot] = PAGE_ID_INVALID;
        return 0;
}

static long sys_alloc_gate(upage_id_t ucon, size_t slot, size_t sslot, size_t islot, size_t rest)
{
        long r;
        struct sys_extra_args args;
        size_t oslot, gslot, usecrecy, uintegrity, uownership, uguard, as, entry;
        uint64_t gatearg0, gatearg1, gatearg2;
        struct label secrecy, integrity, ownership, guard;
        usymlink_t upud;

        r = copy_from_user(&args, rest, 11);
        if (r)
                return r;
        oslot = args.extra0;
        gslot = args.extra1;
        usecrecy = args.extra2;
        uintegrity = args.extra3;
        uownership = args.extra4;
        uguard = args.extra5;
        as = args.extra6;
        entry = args.extra7;
        gatearg0 = args.extra8;
        gatearg1 = args.extra9;
        gatearg2 = args.extra10;
        if (r)
                return r;
        r = copy_from_user(secrecy.tags, usecrecy, sizeof(secrecy.tags) / sizeof(uint64_t));
        if (r)
                return r;
        r = copy_from_user(integrity.tags, uintegrity, sizeof(integrity.tags) / sizeof(uint64_t));
        if (r)
                return r;
        r = copy_from_user(ownership.tags, uownership, sizeof(ownership.tags) / sizeof(uint64_t));
        if (r)
                return r;
        r = copy_from_user(guard.tags, uguard, sizeof(guard.tags) / sizeof(uint64_t));
        if (r)
                return r;
        r = copy_from_user(&upud, as, sizeof(usymlink_t) / sizeof(uint64_t));
        if (r)
                return r;
        return do_alloc_gate(ucon, slot, sslot, islot, oslot, gslot, &secrecy, &integrity,
                             &ownership, &guard, upud.upage, upud.uparent, entry, gatearg0, gatearg1, gatearg2);
}

long do_alloc_directory_pud(upage_id_t ucon, size_t slot, size_t sslot, size_t islot, struct label *secrecy, struct label *integrity)
{
        return alloc_page(ucon, slot, sslot, islot, secrecy, integrity, PAGE_TYPE_PUD);
}

static long sys_alloc_directory_pud(upage_id_t ucon, size_t slot, size_t sslot, size_t islot, size_t rest)
{
        int r;
        struct sys_extra_args args;
        struct label secrecy;
        struct label integrity;

        r = copy_from_user(&args, rest, 2);
        if (r)
                return r;
        r = copy_from_user(secrecy.tags, args.extra0, sizeof(secrecy.tags) / sizeof(uint64_t));
        if (r)
                return r;
        r = copy_from_user(integrity.tags, args.extra1, sizeof(integrity.tags) / sizeof(uint64_t));
        if (r)
                return r;

        return do_alloc_directory_pud(ucon, slot, sslot, islot, &secrecy, &integrity);
}

long do_alloc_directory_pmd(upage_id_t ucon, size_t slot, size_t sslot, size_t islot, struct label *secrecy, struct label *integrity)
{
        return alloc_page(ucon, slot, sslot, islot, secrecy, integrity, PAGE_TYPE_PMD);
}

static long sys_alloc_directory_pmd(upage_id_t ucon, size_t slot, size_t sslot, size_t islot, size_t rest)
{
        int r;
        struct sys_extra_args args;
        struct label secrecy;
        struct label integrity;

        r = copy_from_user(&args, rest, 2);
        if (r)
                return r;
        r = copy_from_user(secrecy.tags, args.extra0, sizeof(secrecy.tags) / sizeof(uint64_t));
        if (r)
                return r;
        r = copy_from_user(integrity.tags, args.extra1, sizeof(integrity.tags) / sizeof(uint64_t));
        if (r)
                return r;

        return do_alloc_directory_pmd(ucon, slot, sslot, islot, &secrecy, &integrity);
}

static long sys_directory_get_slot(upage_id_t usym, size_t slot, size_t to)
{
        kpage_id_t ksym;
        usymlink_t uobj;

        if (!(slot < DIRECTORY_NR_ENTRIES))
                return -EINVAL;
        upage_to_kpage(&usym, &ksym);
        if (!kpage_is_type(ksym, PAGE_TYPE_PUD) &&
            !kpage_is_type(ksym, PAGE_TYPE_PMD))
                return -EINVAL;
        if (!thread_can_read_page(get_current_thread(), ksym.id))
                return -EACCES;
        ksymlink_t direntry = directory_get(ksym.id, slot);
        ksymlink_to_usymlink(&direntry, &uobj);
        return copy_to_user(to, &uobj, sizeof(ksymlink_t) / sizeof(uint64_t));
}

static long sys_directory_link_pmd(upage_id_t upud, size_t pudslot, upage_id_t ucon, size_t slot)
{
        kpage_id_t kpud, kcon;
        struct container *container;

        if (!(pudslot < DIRECTORY_NR_ENTRIES))
                return -EINVAL;
        if (!(slot < CONTAINER_NR_PAGES))
                return -EINVAL;
        upage_to_kpage(&upud, &kpud);
        if (!kpage_is_type(kpud, PAGE_TYPE_PUD))
                return -EINVAL;
        if (!thread_can_read_write_page(get_current_thread(), kpud.id))
                return -EACCES;
        upage_to_kpage(&ucon, &kcon);
        if (!kpage_is_type(kcon, PAGE_TYPE_CONTAINER))
                return -EINVAL;
        if (!thread_can_read_page(get_current_thread(), kcon.id))
                return -EACCES;
        container = page_data(kcon.id);
        if (!page_is_type(container->pages[slot], PAGE_TYPE_PMD))
                return -EINVAL;

        return directory_put(kpud.id, pudslot, __ksymlink(__kpage_id(container->pages[slot]), kcon));
}

long do_directory_link_block(upage_id_t upmd, size_t pmdslot, upage_id_t ucon, size_t slot, pteval_t perm)
{
        kpage_id_t kpmd, kcon;
        struct container *container;

        if (!(pmdslot < DIRECTORY_NR_ENTRIES))
                return -EINVAL;
        if (!(slot < CONTAINER_NR_PAGES))
                return -EINVAL;
        upage_to_kpage(&upmd, &kpmd);
        if (!kpage_is_type(kpmd, PAGE_TYPE_PMD))
                return -EINVAL;
        if (!thread_can_read_write_page(get_current_thread(), kpmd.id))
                return -EACCES;
        upage_to_kpage(&ucon, &kcon);
        if (!kpage_is_type(kcon, PAGE_TYPE_CONTAINER))
                return -EINVAL;
        if (!thread_can_read_page(get_current_thread(), kcon.id))
                return -EACCES;
        container = page_data(kcon.id);
        if (!page_is_type(container->pages[slot], PAGE_TYPE_BLOCK))
                return -EINVAL;

        return directory_link(kpmd.id, pmdslot, __ksymlink(__kpage_id(container->pages[slot]), kcon), perm);
}

static long sys_directory_link_block(upage_id_t upmd, size_t pmdslot, upage_id_t ucon, size_t rest)
{
        int r;
        struct sys_extra_args args;
        size_t slot;
        pteval_t perm;

        r = copy_from_user(&args, rest, 2);
        if (r)
                return r;
        slot = args.extra0;
        perm = args.extra1;
        return do_directory_link_block(upmd, pmdslot, ucon, slot, perm);
}

static long sys_directory_unlink_pmd(upage_id_t upud, size_t pudslot)
{
        long r;
        kpage_id_t kpud;
        if (!(pudslot < DIRECTORY_NR_ENTRIES))
                return -EINVAL;
        upage_to_kpage(&upud, &kpud);
        if (!kpage_is_type(kpud, PAGE_TYPE_PUD))
                return -EINVAL;
        if (!thread_can_read_write_page(get_current_thread(), kpud.id))
                return -EACCES;
        r = directory_unlink(kpud.id, pudslot);
        if (r == 0)
                cpu_invalidate_pgtable();
        return r;

}

static long sys_directory_unlink_block(upage_id_t upmd, size_t pmdslot)
{
        long r;
        kpage_id_t kpmd;
        if (!(pmdslot < DIRECTORY_NR_ENTRIES))
                return -EINVAL;
        upage_to_kpage(&upmd, &kpmd);
        if (!kpage_is_type(kpmd, PAGE_TYPE_PMD))
                return -EINVAL;
        if (!thread_can_read_write_page(get_current_thread(), kpmd.id))
                return -EACCES;
        r = directory_unlink(kpmd.id, pmdslot);
        if (r == 0)
                cpu_invalidate_pgtable();
        return r;
}

static long sys_free_gate(upage_id_t ucon, size_t slot)
{
        return free_page(ucon, slot, PAGE_TYPE_GATE);
}

static long sys_free_block(upage_id_t ucon, size_t slot)
{
        return free_page(ucon, slot, PAGE_TYPE_BLOCK);
}

static long sys_free_directory_pud(upage_id_t ucon, size_t slot)
{
        return free_page(ucon, slot, PAGE_TYPE_PUD);
}

static long sys_free_directory_pmd(upage_id_t ucon, size_t slot)
{
        return free_page(ucon, slot, PAGE_TYPE_PMD);
}

static long sys_free_thread(upage_id_t ucon, size_t slot)
{
        return free_page(ucon, slot, PAGE_TYPE_THREAD);
}

static long sys_free_container(upage_id_t ucon, size_t slot)
{
        return free_page(ucon, slot, PAGE_TYPE_CONTAINER);
}

static long sys_page_get_type(upage_id_t ucon, size_t slot, size_t to)
{
        kpage_id_t kcon;
        page_id_t id;
        struct page *page;
        struct container *container;

        if (!(slot < CONTAINER_NR_PAGES))
                return -EINVAL;
        upage_to_kpage(&ucon, &kcon);
        if (!kpage_is_type(kcon, PAGE_TYPE_CONTAINER))
                return -EINVAL;
        if (!thread_can_read_page(get_current_thread(), kcon.id))
                return -EACCES;
        container = page_data(kcon.id);
        id = container->pages[slot];
        if (!page_is_valid(id))
                return -EINVAL;
        page = page_get(id);
        return copy_to_user(to, &page->type, 1);
}

static long sys_page_get_label(upage_id_t ucon, size_t slot, size_t sto, size_t ito)
{
        kpage_id_t kcon;
        page_id_t id;
        struct page *page;
        struct container *container;
        struct label *secrecy, *integrity;

        if (!(slot < CONTAINER_NR_PAGES))
                return -EINVAL;
        upage_to_kpage(&ucon, &kcon);
        if (!kpage_is_type(kcon, PAGE_TYPE_CONTAINER))
                return -EINVAL;
        if (!thread_can_read_page(get_current_thread(), kcon.id))
                return -EACCES;
        container = page_data(kcon.id);
        id = container->pages[slot];
        if (!page_is_valid(id))
                return -EINVAL;
        /* untyped pages do not have labels */
        if (page_is_type(id, PAGE_TYPE_UNTYPED))
                return -EINVAL;
        /* thread's labels are mutable and therefore not readable */
        if (page_is_type(id, PAGE_TYPE_THREAD))
                return -EINVAL;
        page = page_get(id);

        if (!tls_is_valid(sto, sizeof(secrecy->tags) / sizeof(uint64_t)))
                return -EINVAL;
        if (!tls_is_valid(ito, sizeof(integrity->tags) / sizeof(uint64_t)))
                return -EINVAL;

        secrecy = page_data(page->secrecy);
        integrity = page_data(page->integrity);
        _copy_to_user(sto, &secrecy->tags, sizeof(secrecy->tags) / sizeof(uint64_t));
        _copy_to_user(ito, integrity->tags, sizeof(integrity->tags) / sizeof(uint64_t));
        return 0;
}

static long sys_gate_get_label(upage_id_t ucon, size_t slot, size_t sto, size_t ito, size_t oto)
{
        kpage_id_t kcon;
        page_id_t id;
        struct page *page;
        struct container *container;
        struct label *secrecy, *integrity, *ownership;

        if (!(slot < CONTAINER_NR_PAGES))
                return -EINVAL;
        upage_to_kpage(&ucon, &kcon);
        if (!kpage_is_type(kcon, PAGE_TYPE_CONTAINER))
                return -EINVAL;
        if (!thread_can_read_page(get_current_thread(), kcon.id))
                return -EACCES;
        container = page_data(kcon.id);
        id = container->pages[slot];
        if (!page_is_valid(id))
                return -EINVAL;

        if (!page_is_type(id, PAGE_TYPE_GATE))
                return -EINVAL;
        page = page_get(id);

        if (!tls_is_valid(sto, sizeof(secrecy->tags) / sizeof(uint64_t)))
                return -EINVAL;
        if (!tls_is_valid(ito, sizeof(integrity->tags) / sizeof(uint64_t)))
                return -EINVAL;
        if (!tls_is_valid(oto, sizeof(ownership->tags) / sizeof(uint64_t)))
                return -EINVAL;

        secrecy = page_data(page->secrecy);
        integrity = page_data(page->integrity);
        ownership = page_data(get_gate(id)->ownership);
        _copy_to_user(sto, &secrecy->tags, sizeof(secrecy->tags) / sizeof(uint64_t));
        _copy_to_user(ito, &integrity->tags, sizeof(integrity->tags) / sizeof(uint64_t));
        _copy_to_user(oto, &ownership->tags, sizeof(ownership->tags) / sizeof(uint64_t));
        return 0;
}

static long sys_page_get_name(upage_id_t ucon, size_t slot, size_t to)
{
        kpage_id_t kcon;
        page_id_t id;
        struct page *page;
        struct container *container;

        if (!(slot < CONTAINER_NR_PAGES))
                return -EINVAL;
        upage_to_kpage(&ucon, &kcon);
        if (!kpage_is_type(kcon, PAGE_TYPE_CONTAINER))
                return -EINVAL;
        if (!thread_can_read_page(get_current_thread(), kcon.id))
                return -EACCES;
        container = page_data(kcon.id);
        id = container->pages[slot];
        if (!page_is_valid(id))
                return -EINVAL;
        if (!page_is_type(id, PAGE_TYPE_UNTYPED) &&
            !thread_can_read_page(get_current_thread(), id))
                return -EACCES;
        page = page_get(id);
        return copy_to_user(to, page->name, PAGE_NAME_LEN / sizeof(uint64_t));
}

static long sys_page_set_name(upage_id_t ucon, size_t slot, size_t from)
{
        kpage_id_t kcon;
        page_id_t id;
        struct page *page;
        struct container *container;
        if (!(slot < CONTAINER_NR_PAGES))
                return -EINVAL;
        upage_to_kpage(&ucon, &kcon);
        if (!kpage_is_type(kcon, PAGE_TYPE_CONTAINER))
                return -EINVAL;
        if (!thread_can_read_page(get_current_thread(), kcon.id))
                return -EACCES;
        container = page_data(kcon.id);
        id = container->pages[slot];
        if (!page_is_valid(id))
                return -EINVAL;
        if (page_is_type(id, PAGE_TYPE_UNTYPED))
            return -EINVAL;
        if (!thread_can_read_write_page(get_current_thread(), id))
                return -EACCES;
        page = page_get(id);
        return copy_from_user(page->name, from, PAGE_NAME_LEN / sizeof(uint64_t));
}

static long sys_page_get_metadata(upage_id_t ucon, size_t slot, size_t to)
{
        kpage_id_t kcon;
        page_id_t id;
        struct page *page;
        struct container *container;

        if (!(slot < CONTAINER_NR_PAGES))
                return -EINVAL;
        upage_to_kpage(&ucon, &kcon);
        if (!kpage_is_type(kcon, PAGE_TYPE_CONTAINER))
                return -EINVAL;
        if (!thread_can_read_page(get_current_thread(), kcon.id))
                return -EACCES;
        container = page_data(kcon.id);
        id = container->pages[slot];
        if (!page_is_valid(id))
                return -EINVAL;
        if (!page_is_type(id, PAGE_TYPE_UNTYPED) &&
            !thread_can_read_page(get_current_thread(), id))
                return -EACCES;
        page = page_get(id);
        return copy_to_user(to, page->metadata, PAGE_METADATA_LEN / sizeof(uint64_t));
}

static long sys_page_set_metadata(upage_id_t ucon, size_t slot, size_t from)
{
        kpage_id_t kcon;
        page_id_t id;
        struct page *page;
        struct container *container;
        if (!(slot < CONTAINER_NR_PAGES))
                return -EINVAL;
        upage_to_kpage(&ucon, &kcon);
        if (!kpage_is_type(kcon, PAGE_TYPE_CONTAINER))
                return -EINVAL;
        if (!thread_can_read_page(get_current_thread(), kcon.id))
                return -EACCES;
        container = page_data(kcon.id);
        id = container->pages[slot];
        if (!page_is_valid(id))
                return -EINVAL;
        if (page_is_type(id, PAGE_TYPE_UNTYPED))
            return -EINVAL;
        if (!thread_can_read_write_page(get_current_thread(), id))
            return -EACCES;
        page = page_get(id);
        return copy_from_user(page->metadata, from, PAGE_METADATA_LEN / sizeof(uint64_t));
}

long do_gate_enter(upage_id_t ucon, size_t slot, struct label *requested_ownership, uintptr_t arg)
{
        page_id_t tid;
        kpage_id_t kcon;
        struct container *container;
        struct gate *gate;
        struct thread *thread;

        struct label *thread_ownership, *gate_ownership, *gate_guard;

        if (!(slot < CONTAINER_NR_PAGES))
                return -EINVAL;
        upage_to_kpage(&ucon, &kcon);
        tid = get_current_thread();
        if (!kpage_is_type(kcon, PAGE_TYPE_CONTAINER))
                return -EINVAL;
        if (!thread_can_read_page(tid, kcon.id))
                return -EACCES;
        container = page_data(kcon.id);
        if (!page_is_type(container->pages[slot], PAGE_TYPE_GATE))
                return -EINVAL;
        if (!thread_can_read_page(tid, container->pages[slot]))
                return -EACCES;

        thread = page_data(tid);
        thread_ownership = get_label(thread->ownership);
        gate = page_data(container->pages[slot]);
        gate_ownership = get_label(gate->ownership);
        gate_guard = get_label(gate->guard);

        if (!label_is_subset(gate_guard, thread_ownership))
                return -EACCES;
        if (!label_is_subsetx(requested_ownership, gate_ownership, thread_ownership))
                return -EACCES;

        set_label(thread->ownership, requested_ownership);

#ifndef __IRPY__
        current_thread_populate_tf();
#endif
        thread_set_gate(thread, gate);
        thread->cpu.rdx = arg;

        sched_run(sched_get_current());

        return 0;
}

static long sys_gate_enter(upage_id_t ucon, size_t slot, size_t uownership, uintptr_t arg)
{
        long r;
        struct label requested_ownership;

        r = copy_from_user(requested_ownership.tags,
                           uownership, sizeof(requested_ownership.tags) / sizeof(uint64_t));
        if (r)
                return r;
        return do_gate_enter(ucon, slot, &requested_ownership, arg);
}

static long sys_thread_get_state(upage_id_t ucon, size_t slot, size_t to)
{
        kpage_id_t kcon;
        struct container *container;
        struct thread *thread;
        page_id_t tid = get_current_thread();
        if (!(slot < CONTAINER_NR_PAGES))
                return -EINVAL;
        upage_to_kpage(&ucon, &kcon);
        if (!kpage_is_type(kcon, PAGE_TYPE_CONTAINER))
                return -EINVAL;
        if (!thread_can_read_page(tid, kcon.id))
                return -EACCES;
        container = page_data(kcon.id);
        if (!page_is_type(container->pages[slot], PAGE_TYPE_THREAD))
                return -EINVAL;
        if (!thread_can_read_page(tid, container->pages[slot]))
                return -EACCES;
        thread = page_data(container->pages[slot]);
        return copy_to_user(to, &thread->state, 1);
}

static long sys_self_get(size_t to)
{
        page_id_t tid;
        ksymlink_t ksym;
        usymlink_t usym;

        tid = get_current_thread();
        struct page *page = page_get(tid);

        ksym.page.id = tid;
        ksym.page.generation = page->generation;
        ksym.parent.id = page->c_parent;
        ksym.parent.generation = page_get(page->c_parent)->generation;
        ksymlink_to_usymlink(&ksym, &usym);
        return copy_to_user(to, &usym, sizeof(ksymlink_t) / sizeof(uint64_t));
}

static long sys_self_get_pud(size_t to)
{
        page_id_t tid;
        struct thread *thread;
        ksymlink_t ksym;
        usymlink_t usym;

        tid = get_current_thread();
        thread = page_data(tid);
        ksym.page.id = thread->mm.page.id;
        ksym.page.generation = thread->mm.page.generation;
        ksym.parent.id = thread->mm.parent.id;
        ksym.parent.generation = thread->mm.parent.generation;
        ksymlink_to_usymlink(&ksym, &usym);
        return copy_to_user(to, &usym, sizeof(ksymlink_t) / sizeof(uint64_t));
}

static long sys_self_get_label(size_t sto, size_t ito, size_t oto)
{
        page_id_t tid;
        struct page *page;
        struct thread *thread;
        struct label *secrecy, *integrity, *ownership;
        tid = get_current_thread();
        page = page_get(tid);
        thread = page_data(tid);

        secrecy = page_data(page->secrecy);
        integrity = page_data(page->integrity);
        ownership = page_data(thread->ownership);

        if (!tls_is_valid(sto, sizeof(secrecy->tags) / sizeof(uint64_t)))
                return -EINVAL;
        if (!tls_is_valid(ito, sizeof(integrity->tags) / sizeof(uint64_t)))
                return -EINVAL;
        if (!tls_is_valid(oto, sizeof(ownership->tags) / sizeof(uint64_t)))
                return -EINVAL;

        _copy_to_user(sto, &secrecy->tags, sizeof(secrecy->tags) / sizeof(uint64_t));
        _copy_to_user(ito, &integrity->tags, sizeof(integrity->tags) / sizeof(uint64_t));
        _copy_to_user(oto, &ownership->tags, sizeof(ownership->tags) / sizeof(uint64_t));
        return 0;
}

long do_self_set_label(struct label *requested_secrecy, struct label *requested_integrity, struct label *requested_ownership)
{
        page_id_t tid;
        struct page *page;
        struct thread *thread;
        struct label *secrecy, *integrity, *ownership;

        tid = get_current_thread();
        page = page_get(tid);
        thread = page_data(tid);

        secrecy = get_label(page->secrecy);
        integrity = get_label(page->integrity);
        ownership = get_label(thread->ownership);

        // Can add any secrecy label and remove any secrecy tag in ownership
        if (!label_is_subsetx(secrecy, requested_secrecy, ownership))
                return -EACCES;
        // Can remove any integrity label and add any from ownership
        if (!label_is_subsetx(requested_integrity, integrity, ownership))
                return -EACCES;
        // Can remove any ownership label
        if (!label_is_subset(requested_ownership, ownership))
                return -EACCES;

        set_label(page->secrecy, requested_secrecy);
        set_label(page->integrity, requested_integrity);
        set_label(thread->ownership, requested_ownership);

        // New label assignment could mean the current process
        // doesn't have permission to run under the current quanta.
        if (!safe_equal(page_id, tid, sched_get_current()))
            sched_run(sched_get_current());

        return 0;
}

static long sys_self_set_label(size_t sfrom, size_t ifrom, size_t ofrom)
{
        long r;
        struct label requested_secrecy, requested_integrity, requested_ownership;

        r = copy_from_user(requested_secrecy.tags, sfrom, sizeof(requested_secrecy.tags) / sizeof(uint64_t));
        if (r)
                return r;
        r = copy_from_user(requested_integrity.tags, ifrom, sizeof(requested_integrity.tags) / sizeof(uint64_t));
        if (r)
                return r;
        r = copy_from_user(requested_ownership.tags, ofrom, sizeof(requested_ownership.tags) / sizeof(uint64_t));
        if (r)
                return r;
        return do_self_set_label(&requested_secrecy, &requested_integrity, &requested_ownership);
}

static long sys_ni_syscall(void)
{
        return -ENOSYS;
}

static long sys_debug_print(size_t slot, size_t len)
{
        printk(-1, "%s", (char*)(tls_entries() + slot));
        return 0;
}

static long sys_debug_getchar(void)
{
        return getchar();
}

static long sys_debug_yield()
{
        current_thread_populate_tf();
        sched_next();
        return 0;
}

static long sys_debug_self_halt(void)
{
        struct thread *thread = page_data(get_current_thread());
        thread->state = THREAD_STATE_HALTED;
        return 0;
}

static long sys_net_transmit(uint64_t buf_idx, size_t len, uint64_t written_idx)
{
        long r, written;
        char buf[SZ_4K];

        if (len > sizeof(buf))
                return -EINVAL;

        if (!thread_can_read_write_page(get_current_thread(), root_container_id))
                return -EACCES;

        if ((r = copy_from_user(buf, buf_idx, roundup(len, sizeof(uint64_t)) / sizeof(uint64_t))))
                return r;

        if (!tls_is_valid(written_idx, 1)) return -EINVAL;

        extern size_t e1000_transmit(void *ptr, size_t len);
        written = e1000_transmit(buf, len);

        _copy_to_user(written_idx, &written, 1);

        return 0;
}

static long sys_net_receive(uint64_t buf_idx, size_t len, uint64_t read_idx)
{
        char buf[SZ_4K];
        long read;
        uint64_t lenprime;

        if (len > sizeof(buf))
                return -EINVAL;

        if (!thread_can_read_write_page(get_current_thread(), root_container_id))
                return -EACCES;

        lenprime = roundup(len, sizeof(uint64_t)) / sizeof(uint64_t);

        if (!tls_is_valid(buf_idx, lenprime)) return -EINVAL;
        if (!tls_is_valid(read_idx, 1)) return -EINVAL;

        extern size_t e1000_receive(void *ptr, size_t len);
        read = e1000_receive(buf, len);

        _copy_to_user(buf_idx, buf, lenprime);
        _copy_to_user(read_idx, &read, 1);

        return 0;
}

void *syscall_table[NR_syscalls] = {
        [0 ... NR_syscalls - 1] = &sys_ni_syscall,
        [SYS_container_get_root] = &sys_container_get_root,
        [SYS_container_get_slot] = &sys_container_get_slot,
        [SYS_container_get_quota] = &sys_container_get_quota,
        [SYS_container_get_uquota] = &sys_container_get_uquota,
        [SYS_container_get_qquota] = &sys_container_get_qquota,
        [SYS_container_move_quota] = &sys_container_move_quota,
        [SYS_container_move_uquota] = &sys_container_move_uquota,
        [SYS_container_move_qquota] = &sys_container_move_qquota,
        [SYS_container_get_parent] = &sys_container_get_parent,
        [SYS_reserve_page] = &sys_reserve_page,
        [SYS_alloc_quantum] = &sys_alloc_quantum,
        [SYS_alloc_tag] = &sys_alloc_tag,
        [SYS_alloc_thread] = &sys_alloc_thread,
        [SYS_alloc_gate] = &sys_alloc_gate,
        [SYS_alloc_block] = &sys_alloc_block,
        [SYS_alloc_container] = &sys_alloc_container,
        [SYS_alloc_directory_pud] = &sys_alloc_directory_pud,
        [SYS_alloc_directory_pmd] = &sys_alloc_directory_pmd,
        [SYS_directory_get_slot] = &sys_directory_get_slot,
        [SYS_directory_link_pmd] = &sys_directory_link_pmd,
        [SYS_directory_link_block] = &sys_directory_link_block,
        [SYS_directory_unlink_pmd] = &sys_directory_unlink_pmd,
        [SYS_directory_unlink_block] = &sys_directory_unlink_block,
        [SYS_free_gate] = &sys_free_gate,
        [SYS_free_block] = &sys_free_block,
        [SYS_free_directory_pud] = &sys_free_directory_pud,
        [SYS_free_directory_pmd] = &sys_free_directory_pmd,
        [SYS_free_thread] = &sys_free_thread,
        [SYS_free_container] = &sys_free_container,
        [SYS_page_get_type] = &sys_page_get_type,
        [SYS_page_get_label] = &sys_page_get_label,
        [SYS_page_get_name] = &sys_page_get_name,
        [SYS_page_set_name] = &sys_page_set_name,
        [SYS_page_get_metadata] = &sys_page_get_metadata,
        [SYS_page_set_metadata] = &sys_page_set_metadata,
        [SYS_gate_enter] = &sys_gate_enter,
        [SYS_gate_get_label] = &sys_gate_get_label,
        [SYS_thread_get_state] = &sys_thread_get_state,
        [SYS_self_get] = &sys_self_get,
        [SYS_self_get_pud] = &sys_self_get_pud,
        [SYS_self_get_label] = &sys_self_get_label,
        [SYS_self_set_label] = &sys_self_set_label,
        [SYS_debug_print] = &sys_debug_print,
        [SYS_debug_getchar] = &sys_debug_getchar,
        [SYS_debug_yield] = &sys_debug_yield,
        [SYS_debug_self_halt] = &sys_debug_self_halt,
        [SYS_debug_uptime] = &uptime,
        [SYS_debug_elapsed_quanta] = &sys_debug_elapsed_quanta,
        [SYS_net_transmit] = &sys_net_transmit,
        [SYS_net_receive] = &sys_net_receive,
};

void usymlink_init(void)
{
        uint8_t key[AES_KEYSIZE_128];

        random_get_bytes(key, sizeof(key));
        aes_set_key(&aes128_ctx, key, sizeof(key));
}
