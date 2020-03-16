#pragma once

#include <sys/types.h>

void udelay(useconds_t usecs);

static inline void ndelay(unsigned long nsecs)
{
        udelay(DIV_ROUND_UP(nsecs, 1000));
}

static inline void mdelay(unsigned long msecs)
{
        udelay(msecs * 1000);
}

#define msleep(msecs)           mdelay(msecs)
#define usleep_range(min, max)  udelay(min)
