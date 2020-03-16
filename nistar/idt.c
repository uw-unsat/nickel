#include <asm/apic.h>
#include <asm/traps.h>
#include <sys/string.h>
#include <uapi/nistar/config.h>

#include "mm.h"
#include "thread.h"
#include "sched.h"

DECLARE_PER_CPU(page_id_t, current_thread);

void do_page_fault(struct pt_regs *regs, long error_code)
{
        uintptr_t va = read_cr2();
        size_t pgd, pud, pmd;
        pgd = pml4_index(va);
        pud = pdpt_index(va);
        pmd = pd_index(va);
        if (thread_handle_pagefault(pgd, pud, pmd, error_code)) {
                pr_err("Failed to handle pgfault at %p (%lu, %lu, %lu)\n", (void*)va, pgd, pud, pmd);
                show_regs(regs);
                die();
        }
}

void smp_spurious_interrupt(struct pt_regs *regs)
{
}

void smp_apic_timer_interrupt(struct pt_regs *regs)
{
        struct thread *thread;
        apic_eoi();
        thread = get_thread(get_current_thread());
        memcpy(&thread->cpu, regs, sizeof(struct pt_regs));
        copy_xregs_to_kernel(&thread->fpu);
        sched_next();
}
