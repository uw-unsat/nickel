#include <nistar/ulib.h>
#include <nistar/env.h>
#include <nistar/fork.h>
#include <unistd.h>
#include <stddef.h>

int system(const char *command)
{
        usymlink_t thread, internal;
        char *argv[] = { "/bin/sh", "-c", (char*) command, NULL };
        extern char **environ;

        internal = self_get_internal_container();

        long r = hs_fork(&thread);
        if (!usymlink_is_valid(thread)) {
                container_move_quota(internal, self_get_internal_container(), 10);
                container_move_uquota(internal, self_get_internal_container(), 10);
                execvpe("/bin/sh", argv, environ);
        }

        wait(NULL);

        return r;
}
