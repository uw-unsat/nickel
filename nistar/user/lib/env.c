#include <nistar/assert.h>
#include <nistar/env.h>
#include <nistar/libfs.h>
#include <nistar/ulib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/wait.h>

// current env / proc

usymlink_t self_get_process_container()
{
        char metadata[PAGE_METADATA_LEN];
        usymlink_t containers[2];
        usymlink_t pud = self_get_pud();
        page_get_metadata(pud, metadata);
        memcpy(containers, metadata, sizeof(containers));
        ASSERT_MSG(usymlink_is_valid(containers[0]),
                   "self_get_internal_container");
        return containers[0];
}

usymlink_t self_get_internal_container()
{
        char metadata[PAGE_METADATA_LEN];
        usymlink_t containers[2];
        usymlink_t pud = self_get_pud();
        page_get_metadata(pud, metadata);
        memcpy(containers, metadata, sizeof(containers));
        ASSERT_MSG(usymlink_is_valid(containers[1]),
                   "self_get_internal_container");
        return containers[1];
}

void self_set_env_containers(usymlink_t process_container, usymlink_t internal_container)
{
        char metadata[PAGE_METADATA_LEN];
        memset(metadata, 0, sizeof(metadata));
        usymlink_t containers[2];
        usymlink_t pud = self_get_pud();

        containers[0] = process_container;
        containers[1] = internal_container;

        ASSERT_MSG(sizeof(containers) <= sizeof(metadata),
                   "metadata too small");
        memcpy(metadata, containers, sizeof(containers));
        page_set_metadata(pud, metadata);
}

void self_set_process_container(usymlink_t cont)
{
        self_set_env_containers(cont, self_get_internal_container());
}

void self_set_internal_container(usymlink_t cont)
{
        self_set_env_containers(self_get_process_container(), cont);
}

long hs_wait4(usymlink_t usym, int *wstatus, int options, struct rusage *rusage, usymlink_t *ret)
{
        if ((options & ~(WNOHANG | WUNTRACED | WCONTINUED)) != 0)
                return -EINVAL;

        usymlink_t inner, obj, cinner, cobj;
        uint64_t type;
        size_t slot, subslot;
        bool has_child = false;
        bool nohang = options & WNOHANG;

        inner = self_get_internal_container();
        // XXX: Currently we are assuming any subcontainer is a proc container.
        // Maybe the current proc should have a `proc` container for children?
loop:
        for (slot = 0; slot < CONTAINER_NR_PAGES; slot++) {
                long r;

                if (container_get_slot(inner, slot, &obj) != 0)
                        continue;
                if (page_get_type(obj, &type) != 0)
                        continue;
                if (type != PAGE_TYPE_CONTAINER)
                        continue;

                // Found a child `proc` container.
                // There should be an internal container in slot 0 of the proc container.
                r = container_get_slot(obj, 0, &cinner);
                ASSERT_MSG(r == 0, "container_get_slot");

                // Look for a thread in the inner container
                for (subslot = 0; subslot < CONTAINER_NR_PAGES; subslot++) {
                        if (container_get_slot(cinner, subslot, &cobj) != 0)
                                continue;
                        if (page_get_type(cobj, &type) != 0)
                                continue;
                        if (type != PAGE_TYPE_THREAD)
                                continue;
                        // Found a child thread
                        has_child = true;

                        // If the usym param is invalid or matches the found thread
                        // we have a match.
                        if (!usymlink_is_valid(usym) || usymlink_eq(usym, cobj)) {
                                if (thread_get_state(cobj) == THREAD_STATE_HALTED) {
                                        // reap cobj
                                        free_page_recursive(obj);
                                        *ret = cobj;
                                        if (wstatus != NULL)
                                                // TODO: pass actual exist status.
                                                // Use 2M block for exit status?
                                                // Use thread metadata?
                                                *wstatus = 0;
                                        return 0;
                                }

                        }
                }
        }

        if (nohang)
                // No children in a waitable state.
                return 0;

        if (!has_child)
                return -ECHILD;

        // Current thread has chlidren and did not specify WNOHANG
        goto loop;
}

noreturn void hs_exit(int status)
{
        // close any open fd
        int i;
        for (i = 0; i < NFILES; i++)
                hs_close(i);

        sys_debug_self_halt();

        while (1) {}

        ASSERT_MSG(false, "TBD");
}
