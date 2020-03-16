#include <nistar/fork.h>
#include <nistar/memlayout.h>
#include <nistar/env.h>
#include <nistar/ulib.h>
#include <string.h>
#include <sys/mman.h>

static long copy_current_pud(usymlink_t *new_pud, usymlink_t ucont, struct label *secrecy, struct label *integrity)
{
        long r;
        size_t i, j;
        void *blkmap;

        usymlink_t pud, pmd, block, new_pmd, new_block;

        pud = self_get_pud();

        r = alloc_directory_pud(new_pud, ucont, secrecy, integrity, "fork");
        ASSERT_MSG(r == 0," alloc_directory_pud");

        // Copy every page up to the shared FS mappings
        // TODO: Copy on write
        for (i = 0; i < pud_index(FS_FILE_MAP_START); i++) {
                if (directory_get_slot(pud, i, &pmd) == 0) {
                        r = alloc_directory_pmd(&new_pmd, ucont, secrecy, integrity, "fork");
                        ASSERT_MSG(r == 0, "alloc_directory_pmd");
                        r = directory_link_pmd(*new_pud, i, new_pmd);
                        for (j = 0; j < DIRECTORY_NR_ENTRIES; j++) {
                                if (directory_get_slot(pmd, j, &block) == 0) {
                                        r = alloc_block(&new_block, ucont, secrecy, integrity, "fork");
                                        ASSERT_MSG(r == 0, "allco_block");
                                        // TODO: Read and copy the current permissions in the current pud.
                                        r = directory_link_block(new_pmd, j, new_block, PTE_PRESENT | PTE_USER | PTE_PSE | PTE_RW);
                                        ASSERT_MSG(r == 0, "directory_link");
                                        blkmap = map_block(0, new_block, PTE_PRESENT | PTE_USER | PTE_PSE | PTE_RW);
                                        ASSERT_MSG(blkmap != 0, "map_block");
                                        memcpy(blkmap, (void*)(SZ_1G * i + SZ_2M * j), SZ_2M);
                                        unmap_block((uintptr_t)blkmap);
                                }
                        }
                }
        }

        // Remap the file mappings into the new AS
        for (i = pud_index(FS_FILE_MAP_START); i < pud_index(FS_FILE_MAP_END); i++) {
                if (directory_get_slot(pud, i, &pmd) == 0) {
                        r = directory_link_pmd(*new_pud, i, pmd);
                        ASSERT_MSG(r == 0, "directory_link_pmd");
                }
        }

        return 0;
}

/*
   Nistar fork. It copies the current AS and spawns a new thread in it.
   Returns the id for the child thread.
*/
long hs_fork(usymlink_t *thread)
{
        long r;
        usymlink_t new_pud, thread_entry_gate, cic, proc, internal;

        char name[PAGE_NAME_LEN];
        char metadata[PAGE_METADATA_LEN];

        struct label secrecy, integrity, ownership, guard;
        self_get_label(&secrecy, &integrity, &ownership);
        label_init(&guard); // TODO: guard

        // Return value for child thread
        *thread = USYMLINK_INVALID;

        cic = self_get_internal_container();

        // TODO: labels for child

        page_get_name(self_get_process_container(), name);
        r = alloc_container(&proc, cic, &secrecy, &integrity, name);
        ASSERT_MSG(r == 0, "alloc_container");
        container_move_quota(cic, proc, 16);

        page_get_name(self_get_internal_container(), name);
        r = alloc_container(&internal, proc, &secrecy, &integrity, name);
        ASSERT_MSG(r == 0, "alloc_container");
        container_move_quota(cic, internal, 256);
        container_move_uquota(cic, internal, 16);
        container_move_qquota(cic, internal, 10);

        extern void _gate_fork_entry();
        extern void __nistar_sys_gate_call_ret();

        void* va = mmap(NULL, SZ_2M, PROT_READ | PROT_WRITE, MAP_PRIVATE, -1, 0);

        uint64_t arg[7] = {
                0, 0, 0, 0, 0, 0, 0
        };

        // Restore callee-save registers to the return of hs_fork
        // TODO:.. this is not correct..
        asm("movq %%rbp, %0" : "=r"(arg[0]));
        asm("movq %%rbx, %0" : "=r"(arg[1]));
        asm("movq %%r12, %0" : "=r"(arg[2]));
        asm("movq %%r13, %0" : "=r"(arg[3]));
        asm("movq %%r14, %0" : "=r"(arg[4]));
        asm("movq %%r15, %0" : "=r"(arg[5]));
        asm("movq %%rdi, %0" : "=r"(arg[6]));

        memcpy(va, (void*)USER_TLS_END - SZ_2M, SZ_2M);

        copy_current_pud(&new_pud, internal, &secrecy, &integrity);

        munmap(va, SZ_2M);

        /* set process containers for child */
        memset(metadata, 0, sizeof(metadata));
        memcpy(metadata, &proc, sizeof(proc));
        memcpy(metadata + sizeof(proc), &internal, sizeof(internal));
        page_set_metadata(new_pud, metadata);

        page_get_name(self_get(), name);
        strncat(name, "-fork-gate", PAGE_NAME_LEN);

        r = alloc_gate(&thread_entry_gate, internal, &secrecy, &integrity,
                        &ownership, &guard, new_pud, _gate_fork_entry,
                        (uint64_t)0, (uint64_t)va, (uintptr_t)arg, name);
        ASSERT_MSG(r == 0, "alloc_gate");

        page_get_name(self_get(), name);
        strncat(name, "-fork-thread", PAGE_NAME_LEN);

        r = alloc_thread(thread, internal,
                         &secrecy, &integrity, &ownership, thread_entry_gate, name);
        ASSERT_MSG(r == 0, "alloc_thread");

        // Give the new thread 10 quanta of scheduling time.
        alloc_quanta(internal, *thread, 10);

        return 0;
}
