#pragma once

#include <asm/io.h>

#define RTC_PORT(x)     (0x70 + (x))

static inline void rtc_cmos_write(unsigned char val, unsigned char addr)
{
        outb(addr, RTC_PORT(0));
        outb(val, RTC_PORT(1));
}
