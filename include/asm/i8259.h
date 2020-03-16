#pragma once

/* i8259A PIC registers */
#define PIC_MASTER_CMD          0x20
#define PIC_MASTER_IMR          0x21
#define PIC_MASTER_ISR          PIC_MASTER_CMD
#define PIC_MASTER_POLL         PIC_MASTER_ISR
#define PIC_MASTER_OCW3         PIC_MASTER_ISR
#define PIC_SLAVE_CMD           0xa0
#define PIC_SLAVE_IMR           0xa1

/* i8259A PIC related value */
#define PIC_CASCADE_IR          2
#define MASTER_ICW4_DEFAULT     0x01
#define SLAVE_ICW4_DEFAULT      0x01
#define PIC_ICW4_AEOI           2

void i8259_init(void);
