#include <fcntl.h>
#include <nistar/assert.h>
#include <nistar/elf.h>
#include <nistar/exec.h>
#include <nistar/memlayout.h>
#include <nistar/env.h>
#include <nistar/ulib.h>
#include <limits.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

long fspawn(int fd, char *const argv[], char *const envp[])
{
        ASSERT_MSG(fd >= 0, "invalid fd");
        long r;
        extern void _gate_entry_with_tls();
        usymlink_t thread_entry_gate, thread;

        // TODO: labels..
        struct label secrecy, integrity, ownership, guard;
        self_get_label(&secrecy, &integrity, &ownership);
        label_init(&guard);

        void* va = mmap(NULL, SZ_2M, PROT_READ | PROT_WRITE, MAP_PRIVATE, -1, 0);

        uint64_t arg[6] = {
                (uint64_t)fd, (uint64_t)argv, (uint64_t)envp, 0, 0, 0
        };

        memcpy(va, (void*)USER_TLS_END - SZ_2M, SZ_2M);

        r = alloc_gate(&thread_entry_gate, self_get_internal_container(), &secrecy, &integrity,
                        &ownership, &guard, self_get_pud(), _gate_entry_with_tls,
                        (uint64_t)hs_fexecve, (uint64_t)va, (uintptr_t)arg, argv[0]);
        ASSERT_MSG(r == 0, "alloc_gate");

        r = alloc_thread(&thread, self_get_internal_container(),
                         &secrecy, &integrity, &ownership, thread_entry_gate, argv[0]);
        ASSERT_MSG(r == 0, "alloc_thread");

        alloc_quantum(self_get_internal_container(), thread);

        // TODO: resource cleanup
        /* munmap(va, SZ_2M); */

        return 0;
}

int spawn(const char *path, char *const argv[], char *const envp[])
{
        int fd = open(path, O_RDONLY);
        ASSERT_MSG(fd >= 0, "spawn: file not found\n");
        return fspawn(fd, argv, envp);
}
