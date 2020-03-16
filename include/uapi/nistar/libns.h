#include <nistar/ulib.h>

#define NS_DATA_MAX 1518

enum ns_op {
        NS_GETHOSTBYNAME,
        NS_SOCKET,
        NS_BIND,
        NS_LISTEN,
        NS_ACCEPT,
        NS_WRITE,
        NS_RECV,
        NS_CLOSE,
        NS_CONNECT,
};

struct ns_response {

        union {
                struct {
                        char addr[32];
                } gethostbyname;

                struct {
                        long fd;
                } socket;

                struct {
                } bind;

                struct {
                } listen;

                struct {
                        long newfd;
                } accept;

                struct {
                } write;
        };

        /* Only for ns internal use */
        int done;
        long err;
};

struct ns_request {
        enum ns_op op;

        union {
                struct {
                        char name[32];
                } gethostbyname;

                struct {
                } socket;

                struct {
                        long fd;
                        char addr[32];
                        uint16_t port;
                } bind;

                struct {
                        long fd;
                        uint8_t backlog;
                } listen;

                struct {
                        long fd;
                } accept;

                struct {
                        long fd;
                        char buf[NS_DATA_MAX];
                        size_t len;
                } write;

                struct {
                        long fd;
                } close;

                struct {
                        long fd;
                        char addr[32];
                        uint16_t port;
                } connect;
        };

        struct ns_response resp;
};

long call_ns_gate(struct ns_request *);

long ns_gethostbyname(const char *name, char *addr);
long ns_socket(long *fd);
long ns_bind(long fd, const char *addr, uint16_t port);
long ns_listen(long fd, uint8_t backlog);
long ns_accept(long fd, long *newfd);
long ns_write(long fd, const char *buf, size_t len);
long ns_close(long fd);
long ns_connect(long fd, const char *addr, uint16_t port);
