#pragma once

#include "mm.h"

struct quantum {
        page_id_t container;
        page_id_t thread;
        quantum_id_t _dummy;
};

struct quantum *quantum_get(quantum_id_t q);

void cpu_invalidate_pgtable(void);
void sched_init(page_id_t root_container, page_id_t init, page_id_t idle);

extern unsigned long sys_debug_elapsed_quanta(void);

noinline void current_thread_populate_tf();
page_id_t sched_get_current();

void sched_next();
noinline void sched_run(page_id_t id);
void user_return(page_id_t tid);
