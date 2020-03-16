#include <asm/segment.h>
#include <sys/ilist.h>
#include <sys/string.h>
#include "elf.h"
#include "param.h"
#include "proc.h"

static struct proc procs[NR_PROCS];
uint64_t current_pid;

struct proc *get_proc(uint64_t pid)
{
        return &procs[pid];
}

void proc_new(uint64_t pid, size_t fileid, uint64_t quota)
{

        struct proc *proc = get_proc(pid);

        proc->state = PROC_STATE_RUN;
        proc->fileid = fileid;
        proc->nr_free_pages = quota;
        proc->nr_children = 0;
#ifndef __IRPY__ // TODO
        ilist_add(procs, pid, PID_IDLE);
        memset(&proc->cpu, 0, sizeof(proc->cpu));
#endif
        proc->cpu.cs = USER_CS;
        proc->cpu.ss = USER_DS;
        proc->cpu.rip = elf_get_entry(fileid);
}
