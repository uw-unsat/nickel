#pragma once

/*
 * IDT vectors usable for external interrupt sources start at 0x20.
 * (0x80 is the syscall vector, 0x30-0x3f are for ISA)
 */
#define FIRST_EXTERNAL_VECTOR           0x20

/*
 * Vectors 0x30-0x3f are used for ISA interrupts.
 *   round up to the next 16-vector boundary
 */
#define ISA_IRQ_VECTOR(irq)             (((FIRST_EXTERNAL_VECTOR + 16) & ~15) + irq)

/*
 * Special IRQ vectors used by the SMP architecture, 0xf0-0xff
 */
#define SPURIOUS_APIC_VECTOR            0xff

#define ERROR_APIC_VECTOR               0xfe

#define LOCAL_TIMER_VECTOR              0xee

#define NR_VECTORS                      256

#define FIRST_SYSTEM_VECTOR             LOCAL_TIMER_VECTOR
