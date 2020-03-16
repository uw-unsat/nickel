#include <asm/io.h>
#include <asm/processor.h>
#include <sys/bug.h>
#include <sys/printk.h>

void panic(const char *fmt, ...)
{
        va_list args;

        va_start(args, fmt);
        vprintk(LOGLEVEL_EMERG, fmt, args);
        va_end(args);

        dump_stack();
        die();
}

void die(void)
{
        /* QEMU's -isa-debug-exit */
        outb(0, 0x501);
        /* Bochs shutdown port */
        outsb(0x8900, "Shutdown", 8);

        while (1)
                halt();
}
