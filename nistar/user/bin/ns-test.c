#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <nistar/env.h>
#include <nistar/ulib.h>
#include <nistar/libns.h>

#define CHECK(f) ({r = f; ASSERT_MSG(r == 0, "%ld\n", r);})

int main(int argc, char *argv[])
{
    struct label integrity, secrecy, ownership;

    self_get_label(&secrecy, &integrity, &ownership);
    label_init(&secrecy);
    label_init(&integrity);
    self_set_label(&secrecy, &integrity, &ownership);

    long fd, connfd;
    long r;

    if (fork() == 0) {

        debug_printf("client\n");

        CHECK(ns_socket(&fd));

        debug_printf("Connecting...\b");
        CHECK(ns_connect(fd, "127.0.0.1", 80));

        debug_printf("Connected\n");

    } else {
        debug_printf("server\n");

        CHECK(ns_socket(&fd));

        CHECK(ns_bind(fd, "127.0.0.1", 80));

        CHECK(ns_listen(fd, 8));


        debug_printf("Accepting...\n");
        CHECK(ns_accept(fd, &connfd));

        debug_printf("Accepted\n");

        const char *msg = "HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\n\r\nHello";
        CHECK(ns_write(connfd, msg, strlen(msg)));

        CHECK(ns_close(connfd));

        CHECK(ns_close(fd));
    }

    return 0;
}
