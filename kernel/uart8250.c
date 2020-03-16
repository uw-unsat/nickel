#include <asm/io.h>
#include <asm/processor.h>
#include <sys/console.h>
#include <sys/errno.h>
#include "serial_reg.h"

#define UART_CLK        115200
#define UART_BAUD       19200

struct uart_port {
        unsigned int iobase;
        struct console console;
};

static struct uart_port ports[] = {
        { .iobase = 0x3f8 },
};

static unsigned int uart8250_in(struct uart_port *port, int offset)
{
        return inb(port->iobase + offset);
}

static void uart8250_out(struct uart_port *port, int offset, int value)
{
        outb(value, port->iobase + offset);
}

static int uart8250_getc(struct console *con)
{
        struct uart_port *port = container_of(con, struct uart_port, console);

        if (!(uart8250_in(port, UART_LSR) & UART_LSR_DR))
                return -EAGAIN;

        return uart8250_in(port, UART_RX);
}

static void uart8250_putc(struct uart_port *port, int c)
{
        unsigned int status, both_empty = UART_LSR_TEMT|UART_LSR_THRE;

        uart8250_out(port, UART_TX, c);

        for (;;) {
                status = uart8250_in(port, UART_LSR);
                if ((status & both_empty) == both_empty)
                        break;
                cpu_relax();
        }
}

static void uart8250_write(struct console *con, const char *s, size_t n)
{
        size_t i;
        struct uart_port *port = container_of(con, struct uart_port, console);

        for (i = 0; i < n; ++i)
                uart8250_putc(port, s[i]);
}

static void init_port(struct uart_port *port)
{
        unsigned int divisor;
        unsigned char c;
        unsigned int ier;

        uart8250_out(port, UART_LCR, 0x3);      /* 8n1 */
        ier = uart8250_in(port, UART_IER);
        uart8250_out(port, UART_IER, ier & UART_IER_UUE); /* no interrupt */
        uart8250_out(port, UART_FCR, 0);        /* no fifo */
        uart8250_out(port, UART_MCR, 0x3);      /* DTR + RTS */

        divisor = UART_CLK / UART_BAUD;
        c = uart8250_in(port, UART_LCR);
        uart8250_out(port, UART_LCR, c | UART_LCR_DLAB);
        uart8250_out(port, UART_DLL, divisor & 0xff);
        uart8250_out(port, UART_DLM, (divisor >> 8) & 0xff);
        uart8250_out(port, UART_LCR, c & ~UART_LCR_DLAB);
}

void uart8250_init(void)
{
        size_t i;
        struct uart_port *port;

        for (i = 0; i < ARRAY_SIZE(ports); ++i) {
                port = &ports[i];
                init_port(port);
                /* no serial port */
                if (uart8250_in(port, UART_LSR) == 0xff)
                        continue;
                port->console.getc = uart8250_getc;
                port->console.write = uart8250_write;
                register_console(&port->console);
        }
}
