#include <asm/ptrace.h>
#include <asm/processor.h>
#include <sys/percpu.h>
#include <sys/types.h>


DECLARE_PER_CPU(uint8_t[PAGE_SIZE], cpu_tss) __aligned(PAGE_SIZE);


void current_thread_tf(struct pt_regs **tf)
{
        struct tss *tss;
        tss = (struct tss*)this_cpu_ptr(&cpu_tss);
        *tf = (struct pt_regs*)(this_cpu_ptr((void*)tss->sp0) - sizeof(struct pt_regs));
}
