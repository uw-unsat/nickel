#define pr_fmt(fmt) __MODULE__ ": " fmt

#include <sys/errno.h>
#include <sys/ethernet.h>
#include <e1000_api.h>

#define FLAG_HAS_FLASH                    BIT_64(1)

struct e1000_adapter {
        struct e1000_hw hw;
        struct pci_dev *dev;
        unsigned long flags;
        struct ethernet net;
};

static const struct pci_device_id e1000_pci_tbl[] = {
        { PCI_VDEVICE(INTEL, E1000_DEV_ID_82540EM) },
        { PCI_VDEVICE(INTEL, E1000_DEV_ID_82574L) },
        { PCI_VDEVICE(INTEL, E1000_DEV_ID_PCH_LPT_I217_LM), FLAG_HAS_FLASH },
        { }     /* terminate list */
};

#define er32(reg) E1000_READ_REG(hw, E1000_##reg)
#define ew32(reg, val) E1000_WRITE_REG(hw, E1000_##reg, val)
#define e1000_flush() E1000_WRITE_FLUSH(hw)

static void e1000_set_rx_mode(struct e1000_hw *hw)
{
        int i, mta_reg_count = MAX_MTA_REG;

        for (i = mta_reg_count - 1; i >= 0 ; i--)
                E1000_WRITE_REG_ARRAY(hw, E1000_MTA, i, 0);
        e1000_flush();
}

static void e1000_setup_rctl(struct e1000_hw *hw)
{
        uint32_t rctl;

        rctl = er32(RCTL);

        rctl |= E1000_RCTL_BAM | E1000_RCTL_SZ_2048 | E1000_RCTL_SECRC;
        ew32(RCTL, rctl);
}

void e1000_configure_tx(struct e1000_hw *hw, struct e1000_tx_desc *tx_desc, size_t n)
{
        uint64_t tdba;
        uint32_t tdlen;

        /* set the Tx Interrupt Delay register */
        ew32(TIDV, 1);
        /* Tx irq moderation */
        ew32(TADV, 1);

        tdba = __pa(tx_desc);
        tdlen = n * sizeof(struct e1000_tx_desc);
        ew32(TDBAL(0), (tdba & ~UINT32_C(0)));
        ew32(TDBAH(0), (tdba >> 32));
        ew32(TDLEN(0), tdlen);
        ew32(TDH(0), 0);
        ew32(TDT(0), 0);
        E1000_WRITE_FLUSH(hw);

        ew32(TCTL, E1000_TCTL_EN | E1000_TCTL_PSP |
                   (E1000_COLLISION_THRESHOLD << E1000_CT_SHIFT) |
                   (E1000_COLLISION_DISTANCE << E1000_COLD_SHIFT));
        ew32(TIPG, 10 |
                   (8 << E1000_TIPG_IPGR1_SHIFT) |
                   (6 << E1000_TIPG_IPGR2_SHIFT));
}

void e1000_configure_rx(struct e1000_hw *hw, struct e1000_rx_desc *rx_desc, size_t n)
{
        uint32_t rdlen, rctl;
        uint64_t rdba;

        /* disable receives while setting up the descriptors */
        rctl = er32(RCTL);
        ew32(RCTL, rctl & ~E1000_RCTL_EN);

        rdba = __pa(rx_desc);
        rdlen = n * sizeof(struct e1000_rx_desc);
        ew32(RDBAL(0), (rdba & ~UINT32_C(0)));
        ew32(RDBAH(0), (rdba >> 32));
        ew32(RDLEN(0), rdlen);
        ew32(RDH(0), 0);
        ew32(RDT(0), n - 1);

        ew32(RDTR, 0);
        ew32(RADV, 0);

        /* enable receives */
        ew32(RCTL, rctl | E1000_RCTL_EN);
}

#define E1000_TX_RING_SIZE      (SZ_4K / sizeof(struct e1000_tx_desc))
#define E1000_RX_RING_SIZE      (SZ_4K / sizeof(struct e1000_rx_desc))

struct e1000_tx_ring {
        struct e1000_tx_desc desc[E1000_TX_RING_SIZE];
        uint8_t data[E1000_TX_RING_SIZE][SZ_4K] __aligned(SZ_4K);
} __aligned(SZ_2M);

struct e1000_rx_ring {
        struct e1000_rx_desc desc[E1000_RX_RING_SIZE];
        uint8_t data[E1000_RX_RING_SIZE][SZ_4K] __aligned(SZ_4K);
} __aligned(SZ_2M);

static size_t test_e1000_transmit(struct e1000_hw *hw, struct e1000_tx_ring *tx_ring, const void *buf, size_t len)
{
        uint32_t tail;
        struct e1000_tx_desc *desc;

        tail = er32(TDT(0));
        BUG_ON(tail >= E1000_TX_RING_SIZE);
        desc = &tx_ring->desc[tail];

        if (!(desc->upper.data & E1000_TXD_STAT_DD)) {
                pr_err("TX ring overflow\n");
                return 0;
        }

        memcpy(tx_ring->data[tail], buf, len);

        /*
         * Set EOP to actually send this packet.
         * Set RS to get DD status bit when sent.
         */
        desc->lower.data = len | E1000_TXD_CMD_EOP | E1000_TXD_CMD_RS | E1000_TXD_CMD_IFCS;
        desc->upper.data = 0;

        /* move the tail pointer */
        ew32(TDT(0), (tail + 1) % E1000_TX_RING_SIZE);

        return 0;
}

static size_t test_e1000_receive(struct e1000_hw *hw, struct e1000_rx_ring *rx_ring, void *buf, size_t len)
{
        uint32_t tail;
        struct e1000_rx_desc *desc;

        tail = (er32(RDT(0)) + 1) % E1000_RX_RING_SIZE;
        desc = &rx_ring->desc[tail];

        /* check if the descriptor has been filled */
        if (!(desc->status & E1000_RXD_STAT_DD))
                return 0;
        BUG_ON(!(desc->status & E1000_RXD_STAT_EOP));

        len = desc->length;
        memcpy(buf, rx_ring->data[tail], len);
        desc->status = 0;

        /* move the tail pointer */
        ew32(RDT(0), tail);

        return len;
}

static struct e1000_tx_ring test_tx_ring;
static struct e1000_rx_ring test_rx_ring;
static struct e1000_hw *test_hw;

#include <sys/if_arp.h>

uint8_t *e1000_mac(void)
{
    return (uint8_t *) &test_hw->mac.addr;
}

static void test_init_rings(void)
{
        struct e1000_tx_ring *tx_ring = &test_tx_ring;
        struct e1000_rx_ring *rx_ring = &test_rx_ring;
        size_t i;

        for (i = 0; i < E1000_TX_RING_SIZE; ++i) {
                struct e1000_tx_desc *desc = &tx_ring->desc[i];

                desc->buffer_addr = __pa(tx_ring->data[i]);
                desc->upper.fields.status = E1000_TXD_STAT_DD;
        }

        for (i = 0; i < E1000_RX_RING_SIZE; ++i)
                rx_ring->desc[i].buffer_addr = __pa(rx_ring->data[i]);
}

static int e1000_probe(struct pci_dev *dev, const struct pci_device_id *ent)
{
        struct e1000_adapter *adapter = pci_dev_priv(dev);
        struct e1000_hw *hw = &adapter->hw;
        int r;
        size_t i;
        uint16_t speed, duplex;

        BUILD_BUG_ON(sizeof(struct e1000_adapter) < PCI_DEV_PRIV_SIZE);

        adapter->dev = dev;
        adapter->flags = ent->driver_data;
        hw->back = dev;

#if 0
        adapter->net.transmit = e1000_transmit;
        adapter->net.receive = e1000_receive;
#endif
        ethernet_register(&adapter->net);

        pci_enable_device_mem(dev);
        pci_set_master(dev);

        hw->bus.pci_cmd_word = pci_read_config_word(dev, PCI_COMMAND);

        hw->vendor_id = dev->vendor;
        hw->device_id = dev->device;
        hw->revision_id = dev->revision;
        hw->subsystem_vendor_id = dev->subsystem_vendor;
        hw->subsystem_device_id = dev->subsystem_device;

        hw->hw_addr = pci_ioremap_bar(dev, BAR_0);

        /*
         * I217 uses flash memory (SPT uses BAR_0 for flash and
         * requires no setup here).
         */
        if ((adapter->flags & FLAG_HAS_FLASH) &&
            (dev->resource[BAR_1].flags & IORESOURCE_MEM) &&
            (hw->mac.type < e1000_pch_spt))
                adapter->hw.flash_address = pci_ioremap_bar(dev, BAR_1);


        r = e1000_setup_init_funcs(hw, TRUE);
        BUG_ON(r);

        r = e1000_get_bus_info(hw);
        BUG_ON(r);

        /* Initialize link parameters. */
        hw->mac.autoneg = 1;
        hw->phy.autoneg_wait_to_complete = 0;
        hw->phy.autoneg_advertised = E1000_ALL_SPEED_DUPLEX;

        hw->mac.report_tx_early = 1;

        r = e1000_check_reset_block(hw);
        if (r) {
                pr_info("PHY reset is blocked due to SOL/IDER session.\n");
                BUG();
        }

        /*
         * Before reading the NVM, reset the controller to
         * put the device in a known good starting state.
         */
        r = e1000_reset_hw(hw);
        BUG_ON(r);

        /*
         * Systems with ASPM and others may see the checksum fail on the first
         * attempt. Let's give it a few tries.
         */
        for (i = 0; i < 2; i++) {
                r = e1000_validate_nvm_checksum(hw);
                if (!r)
                        break;
        }
        if (r) {
                pr_err("NVM checksum invalid\n");
                BUG();
        }

        r = e1000_read_mac_addr(hw);
        BUG_ON(r);

        pr_info("ether %pM\n", hw->mac.addr);

        r = e1000_get_speed_and_duplex(hw, &speed, &duplex);
        BUG_ON(r);
        pr_info("link is up %d Mbps %s duplex\n",
                speed, duplex == FULL_DUPLEX ? "full" : "half");

        /* FIXME: set flash_address */

        e1000_set_rx_mode(hw);
        e1000_setup_rctl(hw);

        test_init_rings();

        e1000_configure_tx(hw, test_tx_ring.desc, E1000_TX_RING_SIZE);

        e1000_configure_rx(hw, test_rx_ring.desc, E1000_RX_RING_SIZE);

        test_hw = hw;
#if 0
        static uint8_t send_data[140];
        static uint8_t recv_data[140];

        struct ethhdr *ethhdr = (void *)send_data;
        memcpy(ethhdr->h_source, hw->mac.addr, 6);
        memset(ethhdr->h_dest, 0xff, 6);
        ethhdr->h_proto = cpu_to_be16(ETH_P_ARP);
        struct arphdr *arphdr = (void *)(ethhdr + 1);
        arphdr->ar_hrd = cpu_to_be16(ARPHRD_ETHER);
        arphdr->ar_pro = cpu_to_be16(ETH_P_IP);
        arphdr->ar_hln = 6;
        arphdr->ar_pln = 4;
        arphdr->ar_op = cpu_to_be16(ARPOP_REQUEST);
        memcpy(arphdr->ar_sha, hw->mac.addr, 6);
        /* 10.0.2.15 */
        arphdr->ar_sip[0] = 10;
        arphdr->ar_sip[1] = 0;
        arphdr->ar_sip[2] = 2;
        arphdr->ar_sip[3] = 15;
        /* 10.0.2.2 */
        arphdr->ar_tip[0] = 10;
        arphdr->ar_tip[1] = 0;
        arphdr->ar_tip[2] = 2;
        arphdr->ar_tip[3] = 2;
        test_e1000_transmit(hw, &test_tx_ring, send_data, sizeof(struct ethhdr) + sizeof(struct arphdr));

        size_t len;
        while ((len = test_e1000_receive(hw, &test_rx_ring, recv_data, sizeof(recv_data))) == 0)
                ;
        for (i = 0; i < len; ++i) {
                if (!(i % 16))
                        pr_info("%04zx:", i);
                pr_cont(" %02x", recv_data[i]);
                if (!((i + 1) % 16))
                        pr_cont("\n");
        }
        if (len % 16)
                pr_cont("\n");
#endif

        return 0;
}

static struct pci_driver e1000_driver = {
        .name = "e1000",
        .id_table = e1000_pci_tbl,
        .probe = e1000_probe,
};

void e1000_init(void)
{
        pci_register_driver(&e1000_driver);
}

size_t e1000_transmit(const void *buf, size_t len)
{
        return test_e1000_transmit(test_hw, &test_tx_ring, buf, len);
}

size_t e1000_receive(void *buf, size_t len)
{
        return test_e1000_receive(test_hw, &test_rx_ring, buf, len);
}

/* stub for e1000 shared code */

static struct pci_dev *to_dev(struct e1000_hw *hw)
{
        return hw->back;
}

void e1000_read_pci_cfg(struct e1000_hw *hw, uint32_t reg, uint16_t *value)
{
        *value = pci_read_config_word(to_dev(hw), reg);
}

void e1000_write_pci_cfg(struct e1000_hw *hw, uint32_t reg, uint16_t *value)
{
        pci_write_config_word(to_dev(hw), reg, *value);
}

void e1000_pci_set_mwi(struct e1000_hw *hw)
{
        pci_write_config_word(to_dev(hw), PCI_COMMAND,
                hw->bus.pci_cmd_word | PCI_COMMAND_INVALIDATE);
}

void e1000_pci_clear_mwi(struct e1000_hw *hw)
{
        pci_write_config_word(to_dev(hw), PCI_COMMAND,
                hw->bus.pci_cmd_word & ~PCI_COMMAND_INVALIDATE);
}

int32_t e1000_read_pcie_cap_reg(struct e1000_hw *hw, uint32_t reg, uint16_t *value)
{
        struct pci_dev *dev = to_dev(hw);
        int offset;

        offset = pci_find_capability(dev, PCI_CAP_ID_EXP);
        if (!offset)
                return -E1000_ERR_CONFIG;

        *value = pci_read_config_word(dev, offset + reg);
        return E1000_SUCCESS;
}
