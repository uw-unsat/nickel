#include <nistar/memlayout.h>
#include <stddef.h>
#include "internal/pthread_impl.h"

/* called by musl */
void __init_tls(size_t *auxv)
{
        /* nothing for now; could use to set up %fs */
        pthread_t td = (pthread_t)USER_TLS_START;

        td->self = td;
        td->locale = &libc.global_locale;
}
