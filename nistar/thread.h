#pragma once

#include <asm/fpu.h>
#include <asm/traps.h>
#include "mm.h"

struct thread {
        page_id_t              ownership;
        page_id_t              local;
        enum thread_state      state;
        ksymlink_t             mm;
        uint64_t               fsbase;
        uint64_t               gsbase;
        struct pt_regs         cpu;
        struct xregs_state     fpu;
        /*
         * WARNING: 'fpu' is dynamically-sized.  Do not put
         * anything after it here.
         */
};

struct thread *get_thread(page_id_t id);

/* make sure fpu has enough space */
void thread_check_xstate_size(void);

int untyped_to_thread(page_id_t id);
int thread_alloc(page_id_t id);
int thread_alloc(page_id_t id);
int thread_free(page_id_t cid, page_id_t id);
page_id_t get_current_thread();

void thread_set_local(page_id_t id, page_id_t local);
noinline void thread_clear_tls(page_id_t tid);

int thread_handle_pagefault(size_t pgd, size_t pud, size_t pmd, long error_code);

bool thread_can_read(page_id_t tid, struct page *other);
bool thread_can_write(page_id_t tid, struct page *other);
bool thread_can_read_write(page_id_t tid, struct page *other);

bool thread_can_read_page(page_id_t tid, page_id_t other);
bool thread_can_write_page(page_id_t tid, page_id_t other);
bool thread_can_read_write_page(page_id_t tid, page_id_t other);
