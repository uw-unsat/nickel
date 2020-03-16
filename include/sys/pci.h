#pragma once

#include <sys/ioport.h>
#include <sys/pci_ids.h>
#include <sys/pci_regs.h>

/*
 * The PCI interface treats multi-function devices as independent
 * devices.  The slot/function address of each device is encoded
 * in a single byte as follows:
 *
 *	7:3 = slot
 *	2:0 = function
 */
#define PCI_DEVFN(slot, func)   ((((slot) & 0x1f) << 3) | ((func) & 0x07))
#define PCI_SLOT(devfn)         (((devfn) >> 3) & 0x1f)
#define PCI_FUNC(devfn)         ((devfn) & 0x07)

#define PCI_ANY_ID (~0)

/**
 * PCI_DEVICE - macro used to describe a specific pci device
 * @vend: the 16 bit PCI Vendor ID
 * @dev: the 16 bit PCI Device ID
 *
 * This macro is used to create a struct pci_device_id that matches a
 * specific device.  The subvendor and subdevice fields will be set to
 * PCI_ANY_ID.
 */
#define PCI_DEVICE(vend,dev) \
        .vendor = (vend), .device = (dev), \
        .subvendor = PCI_ANY_ID, .subdevice = PCI_ANY_ID

/**
 * PCI_DEVICE_SUB - macro used to describe a specific pci device with subsystem
 * @vend: the 16 bit PCI Vendor ID
 * @dev: the 16 bit PCI Device ID
 * @subvend: the 16 bit PCI Subvendor ID
 * @subdev: the 16 bit PCI Subdevice ID
 *
 * This macro is used to create a struct pci_device_id that matches a
 * specific device with subsystem information.
 */
#define PCI_DEVICE_SUB(vend, dev, subvend, subdev) \
        .vendor = (vend), .device = (dev), \
        .subvendor = (subvend), .subdevice = (subdev)

/**
 * PCI_DEVICE_CLASS - macro used to describe a specific pci device class
 * @dev_class: the class, subclass, prog-if triple for this device
 * @dev_class_mask: the class mask for this device
 *
 * This macro is used to create a struct pci_device_id that matches a
 * specific PCI class.  The vendor, device, subvendor, and subdevice
 * fields will be set to PCI_ANY_ID.
 */
#define PCI_DEVICE_CLASS(dev_class,dev_class_mask) \
        .class = (dev_class), .class_mask = (dev_class_mask), \
        .vendor = PCI_ANY_ID, .device = PCI_ANY_ID, \
        .subvendor = PCI_ANY_ID, .subdevice = PCI_ANY_ID

/**
 * PCI_VDEVICE - macro used to describe a specific pci device in short form
 * @vend: the vendor name
 * @dev: the 16 bit PCI Device ID
 *
 * This macro is used to create a struct pci_device_id that matches a
 * specific PCI device.  The subvendor, and subdevice fields will be set
 * to PCI_ANY_ID. The macro allows the next field to follow as the device
 * private data.
 */

#define PCI_VDEVICE(vend, dev) \
        .vendor = PCI_VENDOR_ID_##vend, .device = (dev), \
        .subvendor = PCI_ANY_ID, .subdevice = PCI_ANY_ID, 0, 0

struct pci_device_id {
        uint32_t vendor, device;        /* Vendor and device ID or PCI_ANY_ID*/
        uint32_t subvendor, subdevice;  /* Subsystem ID's or PCI_ANY_ID */
        uint32_t class, class_mask;     /* (class,subclass,prog-if) triplet */
        unsigned long driver_data;      /* Data private to the driver */
};

#define PCI_DEV_PRIV_ALIGN      32
#define PCI_DEV_PRIV_OFFSET     ALIGN(sizeof(struct pci_dev), PCI_DEV_PRIV_ALIGN)
#define PCI_DEV_PRIV_SIZE       (SZ_4K - PCI_DEV_PRIV_OFFSET)

struct pci_dev {
        struct list_head node;
        unsigned int bus;               /* bus this device is on */
        unsigned int devfn;             /* encoded device & function index */
        unsigned short vendor;
        unsigned short device;
        unsigned short subsystem_vendor;
        unsigned short subsystem_device;
        unsigned int class;             /* 3 bytes: (base,sub,prog-if) */
        uint8_t revision;               /* PCI revision, low byte of class word */
        uint8_t hdr_type;               /* PCI header type (`multi' flag masked out) */
        struct pci_driver *driver;	/* which driver has allocated this device */
        struct resource resource[6];    /* IO/memory regions */
        bool multifunction;             /* Part of multi-function device */
};

struct pci_driver {
        struct list_head node;
        const char *name;
        const struct pci_device_id *id_table;   /* must be non-NULL for probe to be called */
        int (*probe)(struct pci_dev *dev, const struct pci_device_id *id);      /* New device inserted */
};

enum {
        BAR_0,
        BAR_1,
        BAR_2,
        BAR_3,
        BAR_4,
        BAR_5,
};

uint8_t pci_read_config_byte(struct pci_dev *dev, int where);
uint16_t pci_read_config_word(struct pci_dev *dev, int where);
uint32_t pci_read_config_dword(struct pci_dev *dev, int where);
void pci_write_config_byte(struct pci_dev *dev, int where, uint8_t val);
void pci_write_config_word(struct pci_dev *dev, int where, uint16_t val);
void pci_write_config_dword(struct pci_dev *dev, int where, uint32_t val);

int pci_find_capability(struct pci_dev *dev, int cap);

void pci_register_driver(struct pci_driver *);

void pci_enable_device_mem(struct pci_dev *dev);
void pci_set_master(struct pci_dev *dev);

void *pci_ioremap_bar(struct pci_dev *dev, int bar);

struct pci_dev *pci_find_device(struct pci_device_id *id, struct pci_dev *from);

static inline struct pci_dev *pci_find_device_by_class(unsigned int class, struct pci_dev *from)
{
        struct pci_device_id id = {
                .vendor = PCI_ANY_ID,
                .device = PCI_ANY_ID,
                .subvendor = PCI_ANY_ID,
                .subdevice = PCI_ANY_ID,
                .class_mask = PCI_ANY_ID,
                .class = class,
        };

        return pci_find_device(&id, from);
}

static inline void *pci_dev_priv(const struct pci_dev *dev)
{
        return (char *)dev + PCI_DEV_PRIV_OFFSET;
}
