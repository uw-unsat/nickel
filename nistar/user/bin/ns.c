#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include <nistar/env.h>
#include <nistar/ulib.h>
#include <nistar/assert.h>
#include <nistar/libns.h>

#include <lwip/dhcp.h>
#include <lwip/dns.h>
#include <lwip/etharp.h>
#include <lwip/inet.h>
#include <lwip/init.h>
#include <lwip/netif.h>
#include <lwip/prot/dhcp.h>
#include <lwip/tcp.h>
#include <lwip/timeouts.h>
#include <lwip/udp.h>

#define DEFAULT_DNS "8.8.8.8"

#define ARRAY_SIZE(arr) (sizeof(arr) / sizeof((arr)[0]))

static bool nslock;

static inline void ns_lock(void)
{
        while (__atomic_test_and_set(&nslock, __ATOMIC_ACQUIRE))
                ;
}

static inline void ns_unlock(void)
{
        __atomic_clear(&nslock, __ATOMIC_RELEASE);
}


/* Static data */
static struct netif e1000_netif;

#if 1
// QEMU
static uint8_t mac[6] = { 0x52, 0x54, 0x00, 0x12, 0x34, 0x56 };
#endif

#if 0
// Helgi's machine
static uint8_t mac[6] = { 0x98, 0x90, 0x96, 0xdd , 0x0a, 0xde };
#endif

static err_t low_level_output(struct netif *netif, struct pbuf *p)
{
        struct pbuf *q;
        int r;

        for (q = p; q != NULL; q = q->next) {
                r = net_transmit(q->payload, q->len);
                // ASSERT(r != 0);
        }
        return ERR_OK;
}

static err_t e1000_netif_init(struct netif *netif)
{
        netif->name[0] = 'e';
        netif->name[1] = 'h';
        netif->output = etharp_output;
        netif->linkoutput = low_level_output;
        netif->hwaddr_len = ETHARP_HWADDR_LEN;
        memcpy(netif->hwaddr, mac, ETHARP_HWADDR_LEN);
        netif->mtu = 1500;
        netif->flags = NETIF_FLAG_BROADCAST | NETIF_FLAG_ETHARP | NETIF_FLAG_ETHERNET;
        return ERR_OK;
}

static int ns_do_timer(void)
{
        static char buf[NS_DATA_MAX];
        size_t n;
        struct netif *netif = &e1000_netif;

        n = net_receive(buf, sizeof(buf));
        if (n) {
                struct pbuf *p, *q;
                size_t copied = 0;

                p = pbuf_alloc(PBUF_RAW, sizeof(buf), PBUF_POOL);
                ASSERT_MSG(p != NULL, "pbuf_alloc failed");
                for (q = p; q != NULL; q = q->next) {
                        size_t len = min((size_t)q->len, n - copied);

                        memcpy(q->payload, buf + copied, len);
                        copied += len;
                }

                if (netif->input(p, netif) != ERR_OK) {
                        printf("Warning: ns: drop packet (%zu bytes)\n", n);
                        pbuf_free(p);
                }
        }

        /* lwIP timers check */
        sys_check_timeouts();

        /* no reply for timer */
        return -1;
}

static void init_netif(struct netif *netif)
{
        char ip[IP4ADDR_STRLEN_MAX], netmask[IP4ADDR_STRLEN_MAX], gw[IP4ADDR_STRLEN_MAX];

        lwip_init();

        // netif_add(netif, IP4_ADDR_ANY, IP4_ADDR_ANY, IP4_ADDR_ANY, NULL, e1000_netif_init, netif_input);
        // netif_set_default(netif);
        // netif_set_link_up(netif);
        // netif_set_up(netif);

        // dhcp_start(netif);
        // printf("dhcp initializing\n");
        // while (!dhcp_supplied_address(netif))
        //         ns_do_timer();

        // ip4addr_ntoa_r(netif_ip4_addr(netif_default), ip, sizeof(ip));
        // ip4addr_ntoa_r(netif_ip4_netmask(netif_default), netmask, sizeof(netmask));
        // ip4addr_ntoa_r(netif_ip4_gw(netif_default), gw, sizeof(gw));
        // printf("ns: inet %s netmask %s broadcast %s\n", ip, netmask, gw);
}

#if 0
static err_t do_tcp_recv(void *arg, struct tcp_pcb *pcb, struct pbuf *p, err_t err)
{
        if (err != ERR_OK) return err;

        while (p) {
                printf("recv: %.*s\n", p->len, p->payload);
                tcp_recved(pcb, p->len);
                struct pbuf *next;
                next = p->next;
                pbuf_free(p);
                p = next;
        }

        const char *msg = "HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\n\r\nHello";
        tcp_write(pcb, msg, strlen(msg), TCP_WRITE_FLAG_COPY);

        return ERR_OK;
}

static err_t do_tcp_sent(void *arg, struct tcp_pcb *pcb, u16_t len)
{
        tcp_close(pcb);

        return ERR_OK;
}

static err_t do_tcp_accept(void *arg, struct tcp_pcb *newpcb, err_t err)
{
        char ip[IP4ADDR_STRLEN_MAX];

        if (err != ERR_OK) return err;

        ip4addr_ntoa_r(&newpcb->remote_ip, ip, sizeof(ip));
        printf("Accepted TCP conenction from %s:%hu on %hu\n", ip, newpcb->remote_port, newpcb->local_port);

        tcp_recv(newpcb, &do_tcp_recv);
        tcp_sent(newpcb, &do_tcp_sent);

        return ERR_OK;
}

static void tcp_test(void)
{
        ip_addr_t bind_addr;
        struct tcp_pcb *bind_pcb;

        bind_pcb = tcp_new();
        ASSERT(bind_pcb != NULL);

        ip4addr_aton("0.0.0.0", &bind_addr);

        ASSERT(tcp_bind(bind_pcb, &bind_addr, 80) == ERR_OK);

        bind_pcb = tcp_listen_with_backlog(bind_pcb, 4);

        tcp_accept(bind_pcb, &do_tcp_accept);

        return;

}

static void dns_test(void)
{
        ip_addr_t addr;
        err_t r;
        const char *name = "google.com";

        printf("Testing DNS \"%s\"\n", name);
        r = dns_gethostbyname_addrtype(name, &addr, &do_dns_found, NULL, LWIP_DNS_ADDRTYPE_IPV4);

        if (r == ERR_OK) {
                do_dns_found(name, &addr, NULL);
        } else if (r == ERR_INPROGRESS) {
        } else { ASSERT(false); }
}
#endif

static void do_dns_found(const char *name, const ip_addr_t *ipaddr, struct ns_response *response)
{

        if (ipaddr)
                ip4addr_ntoa_r(ipaddr, response->gethostbyname.addr, 32);

        __atomic_store_n(&response->done, 1, __ATOMIC_RELEASE);
}

/*
 * Sockets
 */

#define NR_SOCKETS 32

struct ns_socket {
        bool inuse;
        struct tcp_pcb *pcb;
};

static struct ns_socket sockets[NR_SOCKETS];

/*
 * Server Operations
 */

static long ns_op_gethostbyname(struct ns_request *request)
{
        err_t r;
        struct ns_response *response;
        ip_addr_t addr;

        debug_printf("ns_op_gethostbyname: %s\r\n", request->gethostbyname.name);


        response = malloc(sizeof(struct ns_response));
        memset(response, 0, sizeof(struct ns_response));

        ns_lock();
        r = dns_gethostbyname_addrtype(request->gethostbyname.name, &addr, (dns_found_callback) &do_dns_found, response, LWIP_DNS_ADDRTYPE_IPV4);
        ns_unlock();
        if (r == ERR_OK) {

                ip4addr_ntoa_r(&addr, request->resp.gethostbyname.addr, 32);

        } else if (r == ERR_INPROGRESS) {
                while (!__atomic_load_n(&response->done, __ATOMIC_ACQUIRE))
                        ;
                r = ERR_OK;
                memcpy(&request->resp, response, sizeof(struct ns_response));
        }

        free(response);
        return r;
}

static long find_fd(void)
{
        for (long i = 0; i < NR_SOCKETS; ++i) {
                if (!sockets[i].inuse) {
                        return i;
                }
        }

        return -1;
}

static long ns_op_socket(struct ns_request *request)
{
        err_t r = ERR_OK;

        ns_lock();

        long fd = find_fd();
        if (fd < 0) {
                r = ERR_MEM; goto done;
        }

        sockets[fd].inuse = true;
        sockets[fd].pcb = tcp_new();

        request->resp.socket.fd = fd;

done:
        ns_unlock();
        return r;
}

static long ns_op_bind(struct ns_request *request)
{
        long fd;
        ip_addr_t addr = {.addr=IPADDR_LOOPBACK};
        err_t r = ERR_OK;

        ns_lock();

        fd = request->bind.fd;

        if (fd >= NR_SOCKETS || !sockets[fd].inuse) {
                r = ERR_ARG; goto done;
        }

        // ip4addr_aton(request->bind.addr, &addr);

        r = tcp_bind(sockets[fd].pcb, &addr, request->bind.port);

done:
        ns_unlock();
        return r;
}


static long ns_op_listen(struct ns_request *request)
{
        long fd;
        err_t r = ERR_OK;

        ns_lock();

        fd = request->bind.fd;
        if (fd >= NR_SOCKETS || !sockets[fd].inuse) {
                r = ERR_ARG; goto done;
        }

        sockets[fd].pcb = tcp_listen_with_backlog(sockets[fd].pcb, request->listen.backlog);

done:
        ns_unlock();
        return r;
}

static err_t do_tcp_accept(struct ns_response *response, struct tcp_pcb *newpcb, err_t err)
{
        if (err != ERR_OK) goto done;

        ASSERT(newpcb != NULL);

        long newfd = find_fd();

        if (newfd < 0) {
                err = ERR_MEM; goto done;
        }

        sockets[newfd].inuse = true;
        sockets[newfd].pcb = newpcb;

        response->accept.newfd = newfd;

done:
        response->err = err;
        __atomic_store_n(&response->done, 1, __ATOMIC_RELEASE);
        return err;
}

static long ns_op_accept(struct ns_request *request)
{
        long fd;
        long r = ERR_OK;
        struct ns_response *response = NULL;

        ns_lock();

        fd = request->accept.fd;
        if (fd >= NR_SOCKETS || !sockets[fd].inuse) {
                r = ERR_ARG; goto done;
        }


        response = malloc(sizeof(struct ns_response));
        memset(response, 0, sizeof(struct ns_response));
        tcp_arg(sockets[fd].pcb, (void *) response);

        tcp_accept(sockets[fd].pcb, (tcp_accept_fn) &do_tcp_accept);

        ns_unlock();
        while (!__atomic_load_n(&response->done, __ATOMIC_ACQUIRE))
                ;
        ns_lock();

        memcpy(&request->resp, response, sizeof(struct ns_response));
        r = response->err;

done:
        if (response) free(response);
        ns_unlock();
        return r;
}

static long ns_op_write(struct ns_request *request)
{
        long fd;
        long r = ERR_OK;

        ns_lock();

        fd = request->write.fd;
        if (fd >= NR_SOCKETS || !sockets[fd].inuse)
                {r = ERR_ARG; goto done; }

        if (request->write.len > NS_DATA_MAX)
                { r = ERR_ARG; goto done; }

        r = tcp_write(sockets[fd].pcb, &request->write.buf, request->write.len, TCP_WRITE_FLAG_COPY);

done:
        ns_unlock();
        return r;
}

static long ns_op_close(struct ns_request *request)
{
        long fd;
        long r = ERR_OK;

        ns_lock();

        fd = request->close.fd;
        if (fd >= NR_SOCKETS || !sockets[fd].inuse)
                {r = ERR_ARG; goto done;}

        r = tcp_close(sockets[fd].pcb);
        if (r != ERR_OK) goto done;

        sockets[fd].inuse = false;
        sockets[fd].pcb = NULL;

done:
        ns_unlock();
        return r;
}

static err_t tcp_do_connected(struct ns_response *arg, struct tcp_pcb *tpcb, err_t err)
{
        arg->err = err;

        __atomic_store_n(&arg->done, 1, __ATOMIC_RELEASE);

        return err;
}

static long ns_op_connect(struct ns_request *request)
{
        long fd;
        long r = ERR_OK;
        ip_addr_t addr = {.addr=IPADDR_LOOPBACK};
        struct ns_response *response = NULL;

        ns_lock();

        fd = request->connect.fd;
        if (fd >= NR_SOCKETS || !sockets[fd].inuse)
                {r = ERR_ARG; goto done;}

        response = malloc(sizeof(struct ns_response));
        memset(response, 0, sizeof(struct ns_response));
        tcp_arg(sockets[fd].pcb, (void *) response);

        // ip4addr_aton(request->connect.addr, &addr);

        r = tcp_connect(sockets[fd].pcb, &addr, request->connect.port, (tcp_connected_fn) &tcp_do_connected);

        ns_unlock();
        while (!__atomic_load_n(&response->done, __ATOMIC_ACQUIRE))
                ;
        ns_lock();

        r = response->err;

done:
        if (response) free(response);
        ns_unlock();
        return r;
}

static void *ns_operations[] = {
        [NS_GETHOSTBYNAME] = &ns_op_gethostbyname,
        [NS_BIND]          = &ns_op_bind,
        [NS_SOCKET]        = &ns_op_socket,
        [NS_LISTEN]        = &ns_op_listen,
        [NS_ACCEPT]        = &ns_op_accept,
        [NS_CLOSE]         = &ns_op_close,
        [NS_WRITE]         = &ns_op_write,
        [NS_CONNECT]       = &ns_op_connect,
};

static long ns_gate_entry(int arg0, struct ns_request *request)
{
        long (*f)() = NULL;
        uint64_t nr = request->op;

        if (nr < ARRAY_SIZE(ns_operations))
                f = ns_operations[nr];

        if (!f) {
                debug_printf("ns operation %ld not implemented\n", nr);
                ASSERT_MSG(false, "");
                return -ENOSYS;
        }

        return f(request);
}

/*
 * Main initialization
 */

noreturn static void ns_init(void)
{
        ip_addr_t dns_addr;
        init_netif(&e1000_netif);

        printf("Setting DNS server to " DEFAULT_DNS "\n");
        ip4addr_aton(DEFAULT_DNS, &dns_addr);
        dns_setserver(0, &dns_addr);


        long r;
        usymlink_t gate;
        struct label secrecy, integrity, ownership, guard;
        self_get_label(&secrecy, &integrity, &ownership);
        label_init(&secrecy);
        label_init(&guard);

        r = alloc_call_gate(&gate, container_get_root(), &secrecy, &integrity,
                            &ownership, &guard, self_get_pud(), &ns_gate_entry, 0, "ns_gate");
        ASSERT_MSG(r == 0, "alloc_call_gate");

        debug_printf("ns_gate created.\n");

        debug_print_label(&secrecy);
        debug_print_label(&integrity);
        debug_print_label(&ownership);

        while (true) {
                ns_lock();
                ns_do_timer();
                ns_unlock();
                sleep(1);
        }
}

int main(int argc, char *argv[])
{
        printf("Intializing network server...\n");
        ns_init();
}
