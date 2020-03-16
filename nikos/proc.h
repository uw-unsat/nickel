#pragma once

#include <asm/traps.h>

enum {
        PROC_STATE_FREE = 0,
        PROC_STATE_RUN,
};

enum {
        PID_IDLE        = 1,
};

struct proc {
        uint64_t state;
        size_t fileid;
        uint64_t nr_free_pages;
        uint64_t nr_children;
        uint64_t prev, next; /* for ready list */
        struct pt_regs cpu;
};

extern uint64_t current_pid;

struct proc *get_proc(uint64_t pid);
void proc_new(uint64_t pid, size_t fileid, uint64_t quota);

static inline struct proc *get_current_proc(void)
{
        return get_proc(current_pid);
}
