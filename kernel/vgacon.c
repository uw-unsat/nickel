#include <asm/io.h>
#include <sys/console.h>
#include <sys/string.h>
#include "vga.h"

/* Base of video memory */
static unsigned long vga_vram_base = 0xb8000;
/* Number of text columns */
static unsigned int vga_video_num_columns = 80;
/* Number of text lines */
static unsigned int vga_video_num_lines = 25 - 1;

/*
 * Use 80x24 as xv6 (to avoid the mess in the last line).
 */

static inline unsigned char vga_rcrt(unsigned char reg)
{
        outb(reg, VGA_CRT_IC);
        return inb(VGA_CRT_DC);
}

static inline void vga_wcrt(unsigned char reg, unsigned char val)
{
        outb(reg, VGA_CRT_IC);
        outb(val, VGA_CRT_DC);
}

static uint16_t vgacon_putc(uint16_t cur, unsigned char c)
{
        uint16_t size = vga_video_num_columns * vga_video_num_lines;
        volatile uint16_t *p = __va(vga_vram_base);

        switch (c) {
        case '\n':
                cur += vga_video_num_columns - cur % vga_video_num_columns;
                break;
        default:
                p[cur] = c | 0x0700;
                cur++;
        }

        if (cur >= size) {
                memmove((void *)p, (void *)(p + vga_video_num_columns),
                        sizeof(uint16_t) * (size - vga_video_num_columns));
                memset((void *)(p + size - vga_video_num_columns), 0,
                        sizeof(uint16_t) * vga_video_num_columns);
                cur -= vga_video_num_columns;
        }

        return cur;
}

static void vgacon_write(struct console *con, const char *s, size_t n)
{
        uint16_t cur;
        size_t i;

        cur = vga_rcrt(VGA_CRTC_CURSOR_HI) << 8;
        cur |= vga_rcrt(VGA_CRTC_CURSOR_LO);

        for (i = 0; i < n; ++i)
                cur = vgacon_putc(cur, s[i]);

        vga_wcrt(VGA_CRTC_CURSOR_HI, cur >> 8);
        vga_wcrt(VGA_CRTC_CURSOR_LO, cur & 0xff);
}

static struct console con = {
        .write = vgacon_write,
};

void vgacon_init(void)
{
        register_console(&con);
}
