#include <asm/msr.h>
#include <asm/setup.h>
#include <sys/percpu.h>
#include <sys/string.h>
#include <uapi/nistar/memlayout.h>

#include "block.h"
#include "container.h"
#include "mm.h"
#include "pgtable.h"
#include "sched.h"
#include "thread.h"
#include "traps.h"

#define PTE_DEFAULT_UMASK (PTE_PRESENT | PTE_USER | PTE_RW)
DEFINE_PER_CPU(page_id_t, current_thread);

/*
 * The quanta based scheduler determines the currently running
 * process. If the current slot is not a valid thread,
 * or that thread does not have sufficient privilege to be
 * executed for the current slot, the kernel idles instead.
 *
 * We consider a couple of different designs for idling, 1) enable interrupts
 * and idle in the kernel until the next interrupt comes in, or 2) designate a
 * idle thread in user space. Option 2) is easier to implement, and so for
 * simplicity we go that route.
 *
 * For our purposes it is important that the idle thread only idles (the only
 * enabled operation is sched_next) which we can achieve in a few different
 * ways:
 *  a) trust the thread to not issue an system calls.
 *  b) assign a high secrecy low integrity label to it to it, effectively
 *     disabling all write operation
 *  c) check at syscall entry that the current thread  is not the idle thread
 *
 * For simplicity we assign a special idle thread that is simply trusted to
 * perform no operation and idles until the next interrupt.
 *
 */
static page_id_t idle;

static quantum_id_t current_ptr;
static struct quantum time[NR_CPUS][SCHED_NR_QUANTA];

/*
 * We want to allow multiple threads to run in the same address space,
 * while each thread has its own local block mapped.  To avoid any
 * interference, each CPU holds a top-level page-table page (PGD/PML4);
 * each address space has PUD/PDPT.  During a context switch, we simply
 * change the PUD pointer in the PGD and the thread-local block.
 *
 * The thread-local block is mapped at virtual address 2MB below 2^47.
 */
static struct pgtable user_pgd[NR_CPUS];
static struct pgtable user_pud[NR_CPUS];
struct pgtable user_pmds[NR_CPUS][PGTABLE_NR_PTES];

static struct pgtable tls_pud[NR_CPUS];
static struct pgtable tls_pmd[NR_CPUS];

#if 0
static struct pgtable pci_pud[NR_CPUS];
#endif

struct quantum *quantum_get(quantum_id_t q)
{
        int cpu = smp_processor_id();
        return &time[cpu][quantum_id_val(q)];
}

noinline void cpu_invalidate_pgtable(void)
{
        int cpu = smp_processor_id();
        /* zero user pmds */
        memset64((void*)user_pmds[cpu], 0, PGTABLE_NR_PTES * PGTABLE_NR_PTES);
}

void sched_init(page_id_t root_container, page_id_t init, page_id_t idle_thread)
{
        int cpu;
        extern pteval_t kpml4[];
        size_t cea_index = pml4_index(CPU_ENTRY_AREA_START);

        idle = idle_thread;

        for_each_possible_cpu(cpu) {
                struct pgtable *pgd, *tpud, *tpmd, *upud;

                pgd = &user_pgd[cpu];
                tpud = &tls_pud[cpu];
                tpmd = &tls_pmd[cpu];
                upud = &user_pud[cpu];

                /* cpu_entry_area mapping */
                pgd->ptes[cea_index] = __pte(kpml4[cea_index]);

                /* tls is placed at 2MB to the top of the lower half */
                pgd->ptes[pml4_index(USER_TLS_START)] = __pte(__pa(tpud) | PTE_DEFAULT_UMASK);
                tpud->ptes[pud_index(USER_TLS_START)] = __pte(__pa(tpmd) | PTE_DEFAULT_UMASK);

                /* pre allocate user's PUDs and PMDsG */
                pgd->ptes[0] = __pte(__pa(upud) | PTE_DEFAULT_UMASK);
                for (size_t i = 0; i < PGTABLE_NR_PTES; i++)
                        upud->ptes[i] = __pte(__pa(user_pmds[cpu][i].ptes) | PTE_DEFAULT_UMASK);

                for (size_t i = 0; i < SCHED_NR_QUANTA; i++) {
                        time[cpu][i].container = root_container;
                        time[cpu][i].thread = init;
                }
                page_get(root_container)->c_qquota = SCHED_NR_QUANTA;

                /* FIXME use real PCI values */
                #if 0
                pgd->ptes[pml4_index(USER_PCI_START)] = __pte(__pa(ppud) | PTE_DEFAULT_UMASK);
                ppud->ptes[pud_index(USER_PCI_START)] = __pte(__pa((void *) (3 * SZ_1G)) | PTE_DEFAULT_UMASK | PTE_PSE);
                #endif

        }
}

unsigned long log_time = 0;

unsigned long sys_debug_elapsed_quanta(void)
{
        return log_time;
}


bool safe_thread_is_runnable(page_id_t id)
{
        if (!page_is_valid(id))
                return 0;
        if (!page_is_type(id, PAGE_TYPE_THREAD))
                return 0;
        return get_thread(id)->state == THREAD_STATE_RUNNABLE;
}

page_id_t sched_get_current()
{
        page_id_t thread, container;
        int cpu = smp_processor_id();

        thread = time[cpu][quantum_id_val(current_ptr)].thread;
        container = time[cpu][quantum_id_val(current_ptr)].container;

        if (safe_thread_is_runnable(thread) && !thread_can_read_page(thread, container))
                thread = idle;
        if (!safe_thread_is_runnable(thread))
                thread = idle;

        return thread;
}

void sched_next()
{
        current_ptr = __quantum_id((quantum_id_val(current_ptr) + 1) % SCHED_NR_QUANTA);
        ++log_time;
        sched_run(sched_get_current());
}

noinline void current_thread_populate_tf()
{
        page_id_t tid;
        struct thread *thread;
        struct pt_regs *tf;

        current_thread_tf(&tf);
        tid = get_current_thread();
        BUG_ON(!page_is_type(tid, PAGE_TYPE_THREAD));
        thread = page_data(tid);

        memcpy(&thread->cpu, tf, sizeof(struct pt_regs));
}

void user_return(page_id_t tid)
{
        int cpu;
        struct thread *thread;
        thread = page_data(tid);
        cpu = smp_processor_id();
        return_to_usermode(&thread->cpu, __pa(&user_pgd[cpu]));
}


noinline void sched_run(page_id_t id)
{
        struct thread *thread;
        int cpu;

        BUG_ON(!page_is_type(id, PAGE_TYPE_THREAD));

        thread = page_data(id);
        BUG_ON(thread->state != THREAD_STATE_RUNNABLE);

        BUG_ON(!ksymlink_is_type(thread->mm, PAGE_TYPE_PUD));

        cpu = smp_processor_id();

        /* invalidate per core pgtable cache */
        cpu_invalidate_pgtable();

        pgtable_link(&tls_pmd[cpu], pmd_index(USER_TLS_START), thread->local, PTE_DEFAULT_UMASK | PTE_PSE);

        per_cpu(current_thread, cpu) = id;

        /* restore fpu */
        copy_kernel_to_xregs(&thread->fpu);

        /* restore user fs/gs */
        wrmsrl(MSR_FS_BASE, thread->fsbase);
        wrmsrl(MSR_KERNEL_GS_BASE, thread->gsbase);

#ifndef __IRPY__
        return_to_usermode(&thread->cpu, __pa(&user_pgd[cpu]));
#endif
}
