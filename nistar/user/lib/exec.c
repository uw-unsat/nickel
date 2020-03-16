#include <elf.h>
#include <fcntl.h>
#include <nistar/assert.h>
#include <nistar/elf.h>
#include <nistar/memlayout.h>
#include <nistar/env.h>
#include <nistar/ulib.h>
#include <limits.h>
#include <string.h>

static size_t reloc_strings(char *v, char **dst, char *const src[], size_t *count, size_t size)
{
        char *nxt;
        size_t i, len = 0;
        for (i = 0; src[i]; i++) {
                nxt = v + len;
                len += strlcpy(v + len, src[i], size - len) + 1;
                ASSERT_MSG(len < size || (src[i+1] == NULL && len <= size),
                           "Can not reloc strings. Not enough space\n");
                dst[i] = nxt;
        }
        dst[i] = NULL;
        *count = i;
        return len;
}

int hs_fexecve(int fd, char *const argv[], char *const envp[])
{
        long r;
        void* entry;
        usymlink_t upud, entry_gate;
        uintptr_t base = 0;

        char name[PAGE_NAME_LEN];
        char metadata[PAGE_METADATA_LEN];

        char saved_argv[PAGE_SIZE];
        char saved_envp[PAGE_SIZE];
        char *sargv[_POSIX_ARG_MAX];
        char *senvp[_POSIX_ARG_MAX];
        size_t argvlen, envplen, argc, envc;

        struct label secrecy, integrity, ownership, guard;
        self_get_label(&secrecy, &integrity, &ownership);
        label_init(&guard); // TODO: guard the execve gate?

        /* relocate argv and envp to lower on the stack as
           we are about to overwrite the top of the stack */
        argvlen = reloc_strings(saved_argv, sargv, argv, &argc, sizeof(saved_argv));
        envplen = reloc_strings(saved_envp, senvp, envp, &envc, sizeof(saved_envp));

        entry = load_elf(fd, &upud, sargv[0], &base);
        ASSERT_MSG(entry != NULL, "load_elf");

        /* copy metadata of current pud to new pud */
        page_get_metadata(self_get_pud(), metadata);
        page_set_metadata(upud, metadata);

        /* change process name */
        if (sargv[0] != NULL) {
                strlcpy(name, sargv[0], sizeof(name));
                page_set_name(self_get(), name);
                strlcat(name, "-proc-container", sizeof(name));
                page_set_name(self_get_process_container(), name);

                strlcpy(name, sargv[0], sizeof(name));
                strlcat(name, "-internal-container", sizeof(name));
                page_set_name(self_get_internal_container(), name);
        }

        strlcpy(name, sargv[0], sizeof(name));
        strlcat(name, "-exec-gate", sizeof(name));

        // Create an entry point in the new address space
        r = alloc_gate(&entry_gate, self_get_internal_container(),
                       &secrecy, &integrity, &ownership, &guard, upud, (void*)entry,
                       0, 0, 0, sargv[0]);
        ASSERT_MSG(r == 0, "alloc_gate");

        void *sp = (void *)USER_STACK_TOP;

        // Copy env to top of stack
        sp -= envplen;
        reloc_strings(sp, senvp, senvp, &envc, envplen);

        // Copy argv below envp
        sp -= argvlen;
        reloc_strings(sp, sargv, sargv, &argc, argvlen);

        // align the stack to 16 bytes
        sp = (void *)rounddown((uintptr_t)sp, 16);
        if ((argc + envc) % 2 != 0)
                sp -= 8;

        // null aux
        sp -= 8;
        memset(sp, 0, 8);

        /* set AUX_BASE */
        sp -= 16;
        *((uint64_t *)sp + 0) = AT_BASE;
        *((uint64_t *)sp + 1) = base;

        // Copy envp pointers
        sp -= (envc * 8 + 8);
        memcpy(sp, senvp, (envc * 8 + 8));

        // Copy argv pointers
        sp -= (argc * 8 + 8);
        memcpy(sp, sargv, (argc * 8 + 8));

        // Copy argc
        sp -= 8;
        memcpy(sp, &argc, 8);

        ASSERT_MSG((uintptr_t)sp % 16 == 0, "stack not aligned: %ld", (uintptr_t)sp % 16);
        // jump to the new AS
        r = gate_enter(entry_gate, &ownership, 0, (uintptr_t)sp);
        ASSERT_MSG(r == 0, "gate_enter");

        // shouldn't reach here
        ASSERT_MSG(false, "TBD");

        __builtin_unreachable();
}

long hs_execve(const char *path, char *const argv[], char *const envp[])
{
        int fd = open(path, O_RDONLY);
        if (fd < 0)
                return fd;
        return hs_fexecve(fd, argv, envp);
}
