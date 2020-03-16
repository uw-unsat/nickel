#include <asm/init.h>
#include <asm/tsc.h>
#include <timer.h>
#include <uip.h>
#include <uip_arp.h>

#define BUF     ((struct uip_eth_hdr *)&uip_buf[0])

size_t e1000_transmit(const void *buf, size_t len);
size_t e1000_receive(void *buf, size_t len);

noreturn void main(void)
{
        int i;
        struct uip_eth_addr eaddr = {
                { 0x52, 0x54, 0x00, 0x12, 0x34, 0x56 }
        };
        uip_ipaddr_t ipaddr;
        struct timer periodic_timer, arp_timer;

        uart8250_init();
        vgacon_init();

        cpu_init();
        tsc_init();

        mtrr_init();

        e1000_init();
        pci_init();

        timer_set(&periodic_timer, CLOCK_SECOND / 2);
        timer_set(&arp_timer, CLOCK_SECOND * 10);

        uip_init();

        uip_setethaddr(eaddr);

        uip_ipaddr(ipaddr, 10,0,2,15);
        uip_sethostaddr(ipaddr);
        uip_ipaddr(ipaddr, 10,0,2,2);
        uip_setdraddr(ipaddr);
        uip_ipaddr(ipaddr, 255,255,255,0);
        uip_setnetmask(ipaddr);

        httpd_init();

        pr_info("httpd: starting\n");

        while (1) {
                uip_len = e1000_receive(uip_buf, UIP_BUFSIZE);
                if (uip_len > 0) {
                        if (BUF->type == htons(UIP_ETHTYPE_IP)) {
                                uip_arp_ipin();
                                uip_input();
                                /*
                                 * If the above function invocation resulted in data that
                                 * should be sent out on the network, the global variable
                                 * uip_len is set to a value > 0.
                                 */
                                if (uip_len > 0) {
                                        uip_arp_out();
                                        e1000_transmit(uip_buf, uip_len);
                                }
                        } else if (BUF->type == htons(UIP_ETHTYPE_ARP)) {
                                uip_arp_arpin();
                                /*
                                 * If the above function invocation resulted in data that
                                 * should be sent out on the network, the global variable
                                 * uip_len is set to a value > 0.
                                 */
                                if (uip_len > 0) {
                                        e1000_transmit(uip_buf, uip_len);
                                }
                        }
                } else if (timer_expired(&periodic_timer)) {
                        timer_reset(&periodic_timer);
                        for (i = 0; i < UIP_CONNS; i++) {
                                uip_periodic(i);
                                /*
                                 * If the above function invocation resulted in data that
                                 * should be sent out on the network, the global variable
                                 * uip_len is set to a value > 0.
                                 */
                                if (uip_len > 0) {
                                        uip_arp_out();
                                        e1000_transmit(uip_buf, uip_len);
                                }
                        }

                        /* Call the ARP timer function every 10 seconds. */
                        if (timer_expired(&arp_timer)) {
                                timer_reset(&arp_timer);
                                uip_arp_timer();
                        }
                }
        }
        die();
}

clock_time_t clock_time(void)
{
        return uptime() / 1000;
}

void uip_log(char *m)
{
        pr_info("uIP: %s\n", m);
}
