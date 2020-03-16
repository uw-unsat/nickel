#pragma once

#include <asm/barrier.h>
#include <asm/io.h>
#include <sys/delay.h>
#include <sys/pci.h>
#include <sys/spinlock.h>
#include <sys/string.h>

#define ASSERT(x)               BUG_ON(x)

#define usec_delay(x)           udelay(x)
#define usec_delay_irq(x)       usec_delay(x)
#define msec_delay(x)           mdelay(x)
#define msec_delay_irq(x)       msec_delay(x)

#define DEBUGOUT(...)           pr_debug(__VA_ARGS__)
#define DEBUGOUT1(...)          DEBUGOUT(__VA_ARGS__)
#define DEBUGOUT2(...)          DEBUGOUT(__VA_ARGS__)
#define DEBUGOUT3(...)          DEBUGOUT(__VA_ARGS__)
#define DEBUGOUT7(...)          DEBUGOUT(__VA_ARGS__)
#define DEBUGFUNC(F)            DEBUGOUT(F "\n")

#define STATIC                  static
#define FALSE                   0
#define TRUE                    1
#define CMD_MEM_WRT_INVALIDATE  PCI_COMMAND_INVALIDATE

#define E1000_MUTEX             struct spinlock
#define E1000_MUTEX_INIT        spinlock_init
#define E1000_MUTEX_DESTROY
#define E1000_MUTEX_LOCK        spin_lock
#define E1000_MUTEX_TRYLOCK     spin_trylock
#define E1000_MUTEX_UNLOCK      spin_unlock

typedef int8_t                  s8;
typedef int16_t                 s16;
typedef int32_t                 s32;
typedef int64_t                 s64;
typedef uint8_t                 u8;
typedef uint16_t                u16;
typedef uint32_t                u32;
typedef uint64_t                u64;

#define E1000_REGISTER(hw, reg) \
        (((hw)->mac.type >= e1000_82543) ? (reg) : e1000_translate_register_82542(reg))

#define E1000_WRITE_FLUSH(hw) \
        E1000_READ_REG(hw, E1000_STATUS)

#define E1000_READ_REG(hw, reg) \
        readl(hw->hw_addr + E1000_REGISTER(hw, reg))

#define E1000_WRITE_REG(hw, reg, value) \
        writel(value, hw->hw_addr + E1000_REGISTER(hw, reg))

#define E1000_READ_REG_ARRAY(hw, reg, index) \
        E1000_READ_REG(hw, E1000_REGISTER(hw, reg) + ((index) << 2))

#define E1000_WRITE_REG_ARRAY(hw, reg, index, value) \
        E1000_WRITE_REG(hw, E1000_REGISTER(hw, reg) + ((index) << 2), value)

#define E1000_READ_REG_ARRAY_DWORD E1000_READ_REG_ARRAY
#define E1000_WRITE_REG_ARRAY_DWORD E1000_WRITE_REG_ARRAY

/* using memory I/O is good enough for QEMU's e1000 */

#define E1000_WRITE_REG_IO(hw, reg, value) \
        E1000_WRITE_REG(hw, reg, value)

/* flash access for ICH8 family */

#define E1000_READ_FLASH_REG(hw, reg) \
        readl(hw->flash_address + (reg))

#define E1000_READ_FLASH_REG16(hw, reg) \
        readw(hw->flash_address + (reg))

#define E1000_WRITE_FLASH_REG(hw, reg, value) \
        writel(value, hw->flash_address + (reg))

#define E1000_WRITE_FLASH_REG16(hw, reg, value) \
        writew(value, hw->flash_address + (reg))
