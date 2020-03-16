#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/wait.h>
#include <unistd.h>
#include <nistar/assert.h>
#include <nistar/env.h>
#include <nistar/fork.h>
#include <nistar/ulib.h>


#define MAX_CHILDREN 5


int main(int argc, char **argv) {
        printf("parent:\n");
        debug_print_usym(self_get());

        while (1) {
                usymlink_t internal;
                uint64_t quota, uquota, qquota;
                internal = self_get_internal_container();
                container_get_quota(internal, &quota);
                container_get_uquota(internal, &uquota);
                container_get_qquota(internal, &qquota);

                usymlink_t child;
                uint64_t children;

                for (children = 0; children < MAX_CHILDREN; children++) {
                        ASSERT_MSG(hs_fork(&child) == 0, "couldn't fork");
                        if (!usymlink_is_valid(child)) {
                                usleep(100000);
                                exit(0);
                        }
                }

                while(children--)
                        wait(NULL);

        }
        return 0;
}
