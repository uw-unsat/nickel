
#include <stdio.h>
#include <string.h>
#include <nistar/env.h>
#include <nistar/ulib.h>
#include <nistar/libns.h>

long call_ns_gate(struct ns_request *arg)
{
        usymlink_t gate;
        long r;

        r = container_find_by_name(container_get_root(), "ns_gate", &gate);
        ASSERT_MSG(r == 0, "find ns_gate");

        r = gate_call(gate, self_get_internal_container(), (uint64_t) arg);

        return r;
}

long ns_gethostbyname(const char *name, char *addr)
{
        struct ns_request req = {
                .op = NS_GETHOSTBYNAME,
                .resp = { .done = false },
        };

        strcpy(req.gethostbyname.name, name);

        long r = call_ns_gate(&req);
        strcpy(addr, req.resp.gethostbyname.addr);

        return r;
}

long ns_socket(long *fd)
{
        struct ns_request req = {
                .op = NS_SOCKET,
                .resp = { .done = false },
        };

        long r = call_ns_gate(&req);

        *fd = req.resp.socket.fd;

        return r;
}

long ns_bind(long fd, const char *addr, uint16_t port)
{
        struct ns_request req = {
                .op = NS_BIND,
                .resp = {.done = false},
        };

        strncpy(req.bind.addr, addr, 32);
        req.bind.fd = fd;
        req.bind.port = port;

        long r = call_ns_gate(&req);

        return r;
}

long ns_listen(long fd, uint8_t backlog)
{
        struct ns_request req = {
                .op = NS_LISTEN,
                .resp = {.done = false},
        };

        req.listen.fd = fd;
        req.listen.backlog = backlog;

        return call_ns_gate(&req);
}

long ns_accept(long fd, long *newfd)
{
        struct ns_request req = {
                .op = NS_ACCEPT,
                .resp = {.done = false},
        };

        req.accept.fd = fd;

        long r = call_ns_gate(&req);

        if (r == 0) *newfd = req.resp.accept.newfd;

        return r;
}

long ns_write(long fd, const char *buf, size_t len)
{
        if (len > NS_DATA_MAX)
                return -1;

        struct ns_request req = {
                .op = NS_WRITE,
                .resp = {.done = false},
        };

        req.write.fd = fd;
        memcpy(&req.write.buf, buf, len);
        req.write.len = len;

        long r = call_ns_gate(&req);

        return r;
}

long ns_close(long fd)
{
        struct ns_request req = {
                .op = NS_CLOSE,
                .resp = {.done = false},
        };

        req.close.fd = fd;

        return call_ns_gate(&req);
}

long ns_connect(long fd, const char *addr, uint16_t port)
{
        struct ns_request req = {
                .op = NS_CONNECT,
                .resp = {.done = false},
        };

        strncpy(req.connect.addr, addr, 32);
        req.connect.port = port;
        req.connect.fd = fd;

        long r = call_ns_gate(&req);

        return r;
}
