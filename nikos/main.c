#include <asm/init.h>
#include <asm/processor.h>
#include "elf.h"
#include "param.h"
#include "proc.h"
#include "vm.h"

noreturn static void user_init(void);

noreturn void main(unsigned int magic, struct multiboot_info *info)
{
        uart8250_init();
        vgacon_init();

        cpu_init();
        tsc_init();

        trap_init();
        syscall_init();

        /* initialize initrd */
        elf_init(info);

        vm_init();
        user_init();
};

static void user_init(void)
{
        uint64_t pid = PID_IDLE;

        /* disable rdtsc/rdtscp for user space */
        cr4_set_bits(X86_CR4_TSD);

        proc_new(pid, ELF_FILE_IDLE, NR_PAGES);
        vm_switch(pid);
}
