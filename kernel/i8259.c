#include <asm/i8259.h>
#include <asm/io.h>
#include <asm/irq.h>
#include <sys/delay.h>

static inline void outb_pic(unsigned char value, unsigned int port)
{
        outb(value, port);
        /*
         * delay for some accesses to PIC on motherboard or in chipset
         * must be at least one microsecond, so be safe here:
         */
        udelay(2);
}

void i8259_init(void)
{
        outb(0xff, PIC_MASTER_IMR);     /* mask all of 8259A-1 */

        /*
         * outb_pic - this has to work on a wide range of PC hardware.
         */
        outb_pic(0x11, PIC_MASTER_CMD); /* ICW1: select 8259A-1 init */

        /* ICW2: 8259A-1 IR0-7 mapped to ISA_IRQ_VECTOR(0) */
        outb_pic(ISA_IRQ_VECTOR(0), PIC_MASTER_IMR);

        /* 8259A-1 (the master) has a slave on IR2 */
        outb_pic(1U << PIC_CASCADE_IR, PIC_MASTER_IMR);

        /* master expects normal EOI */
        outb_pic(MASTER_ICW4_DEFAULT, PIC_MASTER_IMR);

        outb_pic(0x11, PIC_SLAVE_CMD);  /* ICW1: select 8259A-2 init */

        /* ICW2: 8259A-2 IR0-7 mapped to ISA_IRQ_VECTOR(8) */
        outb_pic(ISA_IRQ_VECTOR(8), PIC_SLAVE_IMR);
        /* 8259A-2 is a slave on master's IR2 */
        outb_pic(PIC_CASCADE_IR, PIC_SLAVE_IMR);
        /* (slave's support for AEOI in flat mode is to be investigated) */
        outb_pic(SLAVE_ICW4_DEFAULT, PIC_SLAVE_IMR);

        udelay(100);            /* wait for 8259A to initialize */

        /* mask all */
        outb(0xff, PIC_MASTER_IMR);
        outb(0xff, PIC_SLAVE_IMR);
}
