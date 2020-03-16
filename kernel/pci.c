#include <asm/io.h>
#include <asm/mtrr.h>
#include <sys/errno.h>
#include <sys/list.h>
#include <sys/pci.h>
#include <sys/string.h>

#define MAX_NR_PCI_DEVS         2

#define PCI_FIND_CAP_TTL        48

#define pci_info(dev, fmt, ...)                                 \
        pr_info("pci %02x:%02x.%d: " fmt, dev->bus,             \
                PCI_SLOT(dev->devfn), PCI_FUNC(dev->devfn),     \
                __VA_ARGS__)

/*
 * Functions for accessing PCI base (first 256 bytes) and extended
 * (4096 bytes per PCI function) configuration space with type 1
 * accesses.
 */

#define PCI_CONF1_ADDRESS(bus, devfn, reg)                      \
        (0x80000000 | ((reg & 0xF00) << 16) | (bus << 16)       \
        | (devfn << 8) | (reg & 0xFC))

static LIST_HEAD(pci_drivers);
static LIST_HEAD(pci_devices);

static uint8_t dev_data[MAX_NR_PCI_DEVS][SZ_4K] __aligned(SZ_4K);
static size_t nr_devs = 0;

static uint32_t pci_conf1_read(unsigned int bus, unsigned int devfn, int reg, int len)
{
        BUG_ON((bus > 255) || (devfn > 255) || (reg > 4095));

        outl(PCI_CONF1_ADDRESS(bus, devfn, reg), 0xCF8);

        switch (len) {
        case 1:
                return inb(0xCFC + (reg & 3));
        case 2:
                return inw(0xCFC + (reg & 2));
        case 4:
                return inl(0xCFC);
        default:
                BUG();
        }
}

static void pci_conf1_write(unsigned int bus, unsigned int devfn, int reg, int len, uint32_t value)
{
        BUG_ON((bus > 255) || (devfn > 255) || (reg > 4095));

        outl(PCI_CONF1_ADDRESS(bus, devfn, reg), 0xCF8);

        switch (len) {
        case 1:
                outb((uint8_t)value, 0xCFC + (reg & 3));
                break;
        case 2:
                outw((uint16_t)value, 0xCFC + (reg & 2));
                break;
        case 4:
                outl((uint32_t)value, 0xCFC);
                break;
        default:
                BUG();
        }
}

#define PCI_OP_READ(size, type, len)                                    \
type pci_read_config_##size                                             \
        (struct pci_dev *dev, int pos)                                  \
{                                                                       \
        return pci_conf1_read(dev->bus, dev->devfn, pos, len);          \
}

#define PCI_OP_WRITE(size, type, len)                                   \
void pci_write_config_##size                                            \
        (struct pci_dev *dev, int pos, type value)                      \
{                                                                       \
        return pci_conf1_write(dev->bus, dev->devfn, pos, len, value);  \
}

PCI_OP_READ(byte, uint8_t, 1)
PCI_OP_READ(word, uint16_t, 2)
PCI_OP_READ(dword, uint32_t, 4)
PCI_OP_WRITE(byte, uint8_t, 1)
PCI_OP_WRITE(word, uint16_t, 2)
PCI_OP_WRITE(dword, uint32_t, 4)

static uint64_t pci_size(uint64_t base, uint64_t maxbase, uint64_t mask)
{
        uint64_t size = mask & maxbase;      /* Find the significant bits */
        if (!size)
                return 0;

        /* Get the lowest of them to find the decode size, and
           from that the extent.  */
        size = (size & ~(size-1)) - 1;

        /* base == maxbase can be valid only if the BAR has
           already been programmed with all 1s.  */
        if (base == maxbase && ((base | size) & mask) != mask)
                return 0;

        return size;
}

static inline unsigned long decode_bar(struct pci_dev *dev, uint32_t bar)
{
        uint32_t mem_type;
        unsigned long flags;

        if ((bar & PCI_BASE_ADDRESS_SPACE) == PCI_BASE_ADDRESS_SPACE_IO) {
                flags = bar & ~PCI_BASE_ADDRESS_IO_MASK;
                flags |= IORESOURCE_IO;
                return flags;
        }

        flags = bar & ~PCI_BASE_ADDRESS_MEM_MASK;
        flags |= IORESOURCE_MEM;
        if (flags & PCI_BASE_ADDRESS_MEM_PREFETCH)
                flags |= IORESOURCE_PREFETCH;

        mem_type = bar & PCI_BASE_ADDRESS_MEM_TYPE_MASK;
        switch (mem_type) {
        case PCI_BASE_ADDRESS_MEM_TYPE_32:
                break;
        case PCI_BASE_ADDRESS_MEM_TYPE_1M:
                /* 1M mem BAR treated as 32-bit BAR */
                break;
        case PCI_BASE_ADDRESS_MEM_TYPE_64:
                flags |= IORESOURCE_MEM_64;
                break;
        default:
                /* mem unknown type treated as 32-bit BAR */
                break;
        }
        return flags;
}

static int pci_read_base(struct pci_dev *dev, unsigned int nr)
{
        uint32_t l = 0, sz = 0, mask;
        uint64_t l64, sz64, mask64;
        unsigned int pos = PCI_BASE_ADDRESS_0 + (nr << 2);
        struct resource *res = &dev->resource[nr];

        mask = ~UINT32_C(0);
        l = pci_read_config_dword(dev, pos);
        pci_write_config_dword(dev, pos, l | mask);
        sz = pci_read_config_dword(dev, pos);
        pci_write_config_dword(dev, pos, l);

        /*
         * All bits set in sz means the device isn't working properly.
         * If the BAR isn't implemented, all bits must be 0.  If it's a
         * memory BAR or a ROM, bit 0 must be clear; if it's an io BAR, bit
         * 1 must be clear.
         */
        if (sz == 0xffffffff)
                sz = 0;

        res->flags = decode_bar(dev, l);
        res->flags |= IORESOURCE_SIZEALIGN;
        if (res->flags & IORESOURCE_IO) {
                l64 = l & PCI_BASE_ADDRESS_IO_MASK;
                sz64 = sz & PCI_BASE_ADDRESS_IO_MASK;
                mask64 = PCI_BASE_ADDRESS_IO_MASK & (uint32_t)IO_SPACE_LIMIT;
        } else {
                l64 = l & PCI_BASE_ADDRESS_MEM_MASK;
                sz64 = sz & PCI_BASE_ADDRESS_MEM_MASK;
                mask64 = (uint32_t)PCI_BASE_ADDRESS_MEM_MASK;
        }

        if (res->flags & IORESOURCE_MEM_64) {
                l = pci_read_config_dword(dev, pos + 4);
                pci_write_config_dword(dev, pos + 4, ~0);
                sz = pci_read_config_dword(dev, pos + 4);
                pci_write_config_dword(dev, pos + 4, l);

                l64 |= ((uint64_t)l << 32);
                sz64 |= ((uint64_t)sz << 32);
                mask64 |= ((uint64_t)~0 << 32);
        }

        if (!sz64)
                goto fail;

        sz64 = pci_size(l64, sz64, mask64);
        BUG_ON(!sz64);

        res->start = l64;
        res->end = l64 + sz64;

        goto out;

fail:
        res->flags = 0;
out:
        if (res->flags)
                pci_info(dev, "BAR %d: %pR\n", nr, res);

        return (res->flags & IORESOURCE_MEM_64) ? 1 : 0;
}

static void pci_read_bases(struct pci_dev *dev)
{
        unsigned int pos;

        for (pos = 0; pos < 6; pos++)
                pos += pci_read_base(dev, pos);
}

static bool pci_match_one_device(const struct pci_device_id *id, const struct pci_dev *dev)
{
        if ((id->vendor == PCI_ANY_ID || id->vendor == dev->vendor) &&
            (id->device == PCI_ANY_ID || id->device == dev->device) &&
            (id->subvendor == PCI_ANY_ID || id->subvendor == dev->subsystem_vendor) &&
            (id->subdevice == PCI_ANY_ID || id->subdevice == dev->subsystem_device) &&
            !((id->class ^ dev->class) & id->class_mask))
                return true;
        return false;
}

static const struct pci_device_id *pci_match_id(const struct pci_device_id *ids,
                                                struct pci_dev *dev)
{
        if (ids) {
                while (ids->vendor || ids->subvendor || ids->class_mask) {
                        if (pci_match_one_device(ids, dev))
                                return ids;
                        ids++;
                }
        }
        return NULL;
}

static int pci_device_probe(struct pci_dev *dev)
{
        struct pci_driver *drv;
        const struct pci_device_id *id;
        int r = -ENODEV;

        list_for_each_entry(drv, &pci_drivers, node) {
                id = pci_match_id(drv->id_table, dev);
                if (!id)
                        continue;
                dev->driver = drv;
                BUG_ON(!drv->probe);
                r = drv->probe(dev, id);
                if (!r)
                        break;
        }

        return r;
}

/* naive allocator from an array */

static struct pci_dev *pci_alloc_dev(int bus)
{
        size_t i = nr_devs;
        struct pci_dev *dev;

        if (i >= MAX_NR_PCI_DEVS)
                return NULL;

        ++nr_devs;
        dev = (struct pci_dev *)dev_data[i];
        memset(dev, 0, SZ_4K);
        dev->bus = bus;
        return dev;
}

static void pci_free_dev(struct pci_dev *dev)
{
        size_t i = nr_devs - 1;

        /* must free the last one */
        BUG_ON((uintptr_t)dev != (uintptr_t)dev_data[i]);
        --nr_devs;
}

static int pci_scan_device(struct pci_dev *dev)
{
        uint32_t l, class;
        uint8_t hdr_type;

        /*
         * We got the reserved Vendor ID that indicates a completion with
         * Configuration Request Retry Status (CRS).  Retry until we get a
         * valid Vendor ID or we time out.
         */
        do {
                l = pci_read_config_dword(dev, PCI_VENDOR_ID);

                /* some broken boards return 0 or ~0 if a slot is empty: */
                if (l == 0xffffffff || l == 0x00000000 ||
                    l == 0x0000ffff || l == 0xffff0000)
                        return -EIO;
        } while ((l & 0xffff) == 0x0001);

        dev->vendor = l & 0xffff;
        dev->device = (l >> 16) & 0xffff;

        hdr_type = pci_read_config_byte(dev, PCI_HEADER_TYPE);
        dev->hdr_type = hdr_type & 0x7f;
        dev->multifunction = !!(hdr_type & 0x80);

        class = pci_read_config_dword(dev, PCI_CLASS_REVISION);
        dev->revision = class & 0xff;
        dev->class = class >> 8;                        /* upper 3 bytes */

        pci_info(dev, "[%04x:%04x] type %02x class %#08x\n",
                 dev->vendor, dev->device, dev->hdr_type, dev->class);

        switch (dev->hdr_type) {                        /* header type */
        case PCI_HEADER_TYPE_NORMAL:                    /* standard header */
                if (class == PCI_CLASS_BRIDGE_PCI)
                        goto bad;
                pci_read_bases(dev);
                dev->subsystem_vendor = pci_read_config_word(dev, PCI_SUBSYSTEM_VENDOR_ID);
                dev->subsystem_device = pci_read_config_word(dev, PCI_SUBSYSTEM_ID);
                break;
        case PCI_HEADER_TYPE_BRIDGE:                    /* bridge header */
                if (class != PCI_CLASS_BRIDGE_PCI)
                        goto bad;
                break;
        case PCI_HEADER_TYPE_CARDBUS:                   /* CardBus bridge header */
                if (class != PCI_CLASS_BRIDGE_CARDBUS)
                        goto bad;
                dev->subsystem_vendor = pci_read_config_word(dev, PCI_CB_SUBSYSTEM_VENDOR_ID);
                dev->subsystem_device = pci_read_config_word(dev, PCI_CB_SUBSYSTEM_ID);
                break;
        default:                                        /* unknown header */
                pr_err("unknown header type %02x, ignoring device\n",
                       dev->hdr_type);
                return -EIO;
        bad:
                pr_err("ignoring class %#08x (doesn't match header type %02x)\n",
                        dev->class, dev->hdr_type);
                return -EIO;
        }

        return pci_device_probe(dev);
}

static unsigned next_fn(struct pci_dev *dev, unsigned fn)
{
        if (dev->multifunction)
                return (fn + 1) % 8;
        return 0;
}

static int pci_scan_slot(int bus, int devfn)
{
        int fn = 0, r;

        do {
                struct pci_dev *dev = pci_alloc_dev(bus);

                if (!dev)
                        return -ENOMEM;
                dev->bus = bus;
                dev->devfn = devfn + fn;

                r = pci_scan_device(dev);
                fn = next_fn(dev, fn);

                if (!r)
                        list_add_tail(&dev->node, &pci_devices);
                else
                        pci_free_dev(dev);
        } while (fn > 0);

        return 0;
}

void pci_init(void)
{
        int bus, devfn;

        for (bus = 0; bus < 256; ++bus) {
                for (devfn = 0; devfn < 0x100; devfn += 8) {
                        if (pci_scan_slot(bus, devfn))
                                return;
                }
        }
}

void pci_register_driver(struct pci_driver *drv)
{
        list_add_tail(&drv->node, &pci_drivers);
}

void pci_enable_device_mem(struct pci_dev *dev)
{
        uint16_t old_cmd, cmd;

        old_cmd = pci_read_config_word(dev, PCI_COMMAND);
        cmd = old_cmd | PCI_COMMAND_MEMORY;
        if (cmd != old_cmd)
                pci_write_config_word(dev, PCI_COMMAND, cmd);
}

void pci_set_master(struct pci_dev *dev)
{
        uint16_t old_cmd, cmd;

        old_cmd = pci_read_config_word(dev, PCI_COMMAND);
        cmd = old_cmd | PCI_COMMAND_MASTER;
        if (cmd != old_cmd)
                pci_write_config_word(dev, PCI_COMMAND, cmd);
}

void *pci_ioremap_bar(struct pci_dev *dev, int bar)
{
        struct resource *res;
        phys_addr_t mmio_start, mmio_end;
        uint8_t mtrr, uniform;

        BUG_ON(bar >= ARRAY_SIZE(dev->resource));
        res = &dev->resource[bar];

        BUG_ON(!(resource_type(res) & IORESOURCE_MEM));

        mmio_start = res->start;
        mmio_end = res->end;

        mtrr = mtrr_type_lookup(mmio_start, mmio_end, &uniform);

        if (mtrr != MTRR_TYPE_UNCACHABLE || !uniform)
                pci_info(dev, "BAR %d %s %suniformly\n",
                         bar, mtrr_attrib_to_str(mtrr), uniform ? "" : "non-");

        return __va(mmio_start);
}

static int pci_find_next_cap_ttl(struct pci_dev *dev, uint8_t pos, int cap, int *ttl)
{
        uint8_t id;

        while ((*ttl)--) {
                pos = pci_read_config_byte(dev, pos);
                if (pos < 0x40)
                        break;
                pos &= ~3;
                id = pci_read_config_byte(dev, pos + PCI_CAP_LIST_ID);
                if (id == 0xff)
                        break;
                if (id == cap)
                        return pos;
                pos += PCI_CAP_LIST_NEXT;
        }
        return 0;
}

static int pci_find_next_cap(struct pci_dev *dev, uint8_t pos, int cap)
{
        int ttl = PCI_FIND_CAP_TTL;

        return pci_find_next_cap_ttl(dev, pos, cap, &ttl);
}

static int pci_bus_find_cap_start(struct pci_dev *dev, uint8_t hdr_type)
{
        uint16_t status;

        status = pci_read_config_word(dev, PCI_STATUS);
        if (!(status & PCI_STATUS_CAP_LIST))
                return 0;

        switch (hdr_type) {
        case PCI_HEADER_TYPE_NORMAL:
        case PCI_HEADER_TYPE_BRIDGE:
                return PCI_CAPABILITY_LIST;
        case PCI_HEADER_TYPE_CARDBUS:
                return PCI_CB_CAPABILITY_LIST;
        default:
                return 0;
        }

        return 0;
}

/**
 * pci_find_capability - query for devices' capabilities
 * @dev: PCI device to query
 * @cap: capability code
 *
 * Tell if a device supports a given PCI capability.
 * Returns the address of the requested capability structure within the
 * device's PCI configuration space or 0 in case the device does not
 * support it.  Possible values for @cap:
 *
 *  %PCI_CAP_ID_PM           Power Management
 *  %PCI_CAP_ID_AGP          Accelerated Graphics Port
 *  %PCI_CAP_ID_VPD          Vital Product Data
 *  %PCI_CAP_ID_SLOTID       Slot Identification
 *  %PCI_CAP_ID_MSI          Message Signalled Interrupts
 *  %PCI_CAP_ID_CHSWP        CompactPCI HotSwap
 *  %PCI_CAP_ID_PCIX         PCI-X
 *  %PCI_CAP_ID_EXP          PCI Express
 */
int pci_find_capability(struct pci_dev *dev, int cap)
{
        int pos;

        pos = pci_bus_find_cap_start(dev, dev->hdr_type);
        if (pos)
                pos = pci_find_next_cap(dev, pos, cap);

        return pos;
}

struct pci_dev *pci_find_device(struct pci_device_id *id, struct pci_dev *from)
{
        if (!from)
                from = list_first_entry(&pci_devices, struct pci_dev, node);

        list_for_each_entry_from(from, &pci_devices, node) {
                if (pci_match_one_device(id, from))
                        return from;
        }

        return NULL;
}
