#include <asm/segment.h>
#include <sys/errno.h>
#include <sys/string.h>

#include "mm.h"
#include "block.h"
#include "container.h"
#include "directory.h"
#include "label.h"
#include "pgtable.h"
#include "thread.h"

extern struct pgtable user_pmds[NR_CPUS][PGTABLE_NR_PTES];

DECLARE_PER_CPU(page_id_t, current_thread);

struct thread *get_thread(page_id_t id)
{
        BUG_ON(!page_is_type(id, PAGE_TYPE_THREAD));
        return page_data(id);
}

void thread_check_xstate_size(void)
{
        size_t size;

        size = PAGE_SIZE - offsetof(struct thread, fpu);
        if (size >= fpu_kernel_xstate_size)
                return;

        panic("xstate buffer too small: %zu < %zu\n",
              size, fpu_kernel_xstate_size);
}

noinline static void thread_init_fpstate(struct thread *thread)
{
        memcpy(&thread->fpu, &init_fpstate.xsave,
               PAGE_SIZE - offsetof(struct thread, fpu));
}

int untyped_to_thread(page_id_t id)
{
        struct page *page;
        struct thread *thread;

        if (!page_is_type(id, PAGE_TYPE_UNTYPED))
                return -EINVAL;

        page = page_get(id);
        page->type = PAGE_TYPE_THREAD;
        thread = get_thread(id);
        thread->ownership = LABEL_EMPTY;
        thread->state = THREAD_STATE_NONE;
        thread->local = PAGE_ID_INVALID;
        thread->mm = (ksymlink_t) { .page = KPAGE_ID_INVALID, .parent = KPAGE_ID_INVALID };
        thread->fsbase = 0;
        thread->gsbase = 0;

        /* initialize cpu state */
        thread->cpu.cs = USER_CS;
        thread->cpu.ss = USER_DS;
        thread->cpu.rflags = X86_RFLAGS_IF;
        /* initialize fpu state */
        thread_init_fpstate(thread);
        return 0;
}

int thread_alloc(page_id_t id)
{
        int r;
        r = page_alloc(id, PAGE_TYPE_UNTYPED);
        if (r)
                return r;
        return untyped_to_thread(id);
}

int thread_free(page_id_t cid, page_id_t id)
{
        struct thread *thread;

        BUG_ON(!page_is_type(id, PAGE_TYPE_THREAD));

        thread = page_data(id);

        if (thread->state != THREAD_STATE_HALTED)
                return -EINVAL;

        container_page_free(cid, thread->ownership);
        container_page_free(cid, page_get(id)->secrecy);
        container_page_free(cid, page_get(id)->integrity);
        container_page_free(cid, id);

        return 0;
}

#ifndef __IRPY__
void thread_clear_tls(page_id_t tid)
{
}
#endif

noinline page_id_t get_current_thread()
{
        return this_cpu_read(current_thread);
}

void thread_set_local(page_id_t id, page_id_t local)
{
        struct thread *thread;
        BUG_ON(!page_is_type(id, PAGE_TYPE_THREAD));
        BUG_ON(!page_is_type(local, PAGE_TYPE_BLOCK));
        thread = page_data(id);
        BUG_ON(page_is_valid(thread->local));
        thread->local = local;
}

int thread_handle_pagefault(size_t pgd, size_t pud, size_t pmd, long error_code)
{
        page_id_t id;
        struct thread *thread;
        ksymlink_t mm_pud, mm_pmd, mm_block;
        struct directory *pudpt, *pmdpt;

        int write = error_code & 0x02;
        int perm = PTE_PRESENT | PTE_USER | PTE_PSE;
        if (write)
                perm |= PTE_RW;

        if (pgd != 0)
                return -1;

        id = get_current_thread();
        thread = get_thread(id);
        mm_pud = thread->mm;
        BUG_ON(!ksymlink_is_type(mm_pud, PAGE_TYPE_PUD));
        if (!ksymlink_is_type(mm_pud, PAGE_TYPE_PUD))
                return -1;
        if (!thread_can_read_page(id, mm_pud.page.id))
                return -1;
        pudpt = page_data(mm_pud.page.id);
        mm_pmd = pudpt->entries[pud];
        if (!ksymlink_is_type(mm_pmd, PAGE_TYPE_PMD))
                return -1;
        if (!thread_can_read_page(id, mm_pmd.page.id))
                return -1;
        pmdpt = page_data(mm_pmd.page.id);
        mm_block = pmdpt->entries[pmd];
        if (!ksymlink_is_type(mm_block, PAGE_TYPE_BLOCK))
                return -1;
        if (!thread_can_read_page(id, mm_block.page.id))
                return -1;
        if (write && !thread_can_write_page(id, mm_block.page.id))
                return -1;

        int cpu = smp_processor_id();
        return pgtable_ksymlink_link(&user_pmds[cpu][pud], pmd, mm_block, perm);
}

bool thread_can_read(page_id_t tid, struct page *other)
{
        struct page *threadp;
        struct thread *thread;

        BUG_ON(!page_is_type(tid, PAGE_TYPE_THREAD));

        threadp = page_get(tid);
        thread = page_data(tid);

        return (labelp_is_subsetx(other->secrecy, threadp->secrecy, thread->ownership) &&
                labelp_is_subsetx(threadp->integrity, other->integrity, thread->ownership));
}

bool thread_can_write(page_id_t tid, struct page *other)
{
        struct page *threadp;
        struct thread *thread;

        BUG_ON(!page_is_type(tid, PAGE_TYPE_THREAD));

        threadp = page_get(tid);
        thread = page_data(tid);

        return (labelp_is_subsetx(threadp->secrecy, other->secrecy, thread->ownership) &&
                labelp_is_subsetx(other->integrity, threadp->integrity, thread->ownership));
}

bool thread_can_read_write(page_id_t tid, struct page *other)
{
        return thread_can_read(tid, other) && thread_can_write(tid, other);
}

bool thread_can_read_page(page_id_t tid, page_id_t other)
{
        return thread_can_read(tid, page_get(other));
}

bool thread_can_write_page(page_id_t tid, page_id_t other)
{
        return thread_can_write(tid, page_get(other));
}

bool thread_can_read_write_page(page_id_t tid, page_id_t other)
{
        return thread_can_read_write(tid, page_get(other));
}
