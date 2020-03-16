#include <nistar/elf.h>
#include <nistar/memlayout.h>
#include <nistar/env.h>
#include <nistar/ulib.h>
#include <io/elf.h>
#include <string.h>
#include <fcntl.h>
#include <unistd.h>

static void *do_load_elf(int fd, usymlink_t *upud, char *name, uintptr_t *basep);

static bool is_elf(Elf64_Ehdr *ehdr)
{
        return !memcmp(ehdr->e_ident, ELFMAG, SELFMAG);
}

void *load_elf(int fd, usymlink_t *upud, char *name, uintptr_t *basep)
{
        *basep = 0;
        return do_load_elf(fd, upud, name, basep);
}

static void *load_interp(int fd, usymlink_t *upud, char *name, uintptr_t *basep, Elf64_Phdr *phdr, size_t phnum)
{
        size_t i;

        for (i = 0; i < phnum; i++, phdr++) {
                char interp[128];
                ssize_t n;
                int ldso;
                void *entry;

                if (phdr->p_type != PT_INTERP)
                        continue;

                ASSERT_MSG(phdr->p_filesz <= sizeof(interp), "PT_INTERP too long");
                n = pread(fd, interp, phdr->p_filesz, phdr->p_offset);
                ASSERT_MSG(n > 0, "cannot read PT_INTERP");
                debug_printf("PT_INTERP: %s\n", interp);

                ldso = open(interp, O_RDONLY);
                if (ldso < 0) {
                        debug_printf("cannot open PT_INTERP: %s\n", interp);
                        break;
                }
                *basep = LDSO_START;
                entry = do_load_elf(ldso, upud, name, basep);
                close(ldso);
                return entry;
        }

        return NULL;
}

static void *do_load_elf(int fd, usymlink_t *upud, char *name, uintptr_t *basep)
{
        long r;
        usymlink_t pud, upmd;
        size_t phnum, i;
        ssize_t n, ni, pmdslot, pudidx = -1;
        uintptr_t vaoff;
        char buf[PAGE_SIZE];
        Elf64_Ehdr *ehdr;
        Elf64_Phdr *phdr;
        void *entry;

        n = read(fd, buf, sizeof(buf));
        ASSERT_MSG(n >= 0, "pread");

        ehdr = (void *)buf;

        if (!is_elf(ehdr)) {
                ASSERT_MSG(false, "not elf");
                return NULL;
        }

        phnum = ehdr->e_phnum;

        ASSERT_MSG(ehdr->e_phoff + sizeof(Elf64_Phdr) * phnum <= sizeof(buf), "too many program headers");

        phdr = (void *)buf + ehdr->e_phoff;

        entry = load_interp(fd, upud, name, basep, phdr, phnum);
        if (entry)
                return entry;

        // Find a free 1GiB range in the current address space.
        // to load the elf file into.
        pud = self_get_pud();
        pmdslot = find_free_directory_slot(pud);
        ASSERT_MSG(pmdslot >= 0, "find_free_directory_slot");
        vaoff = SZ_1G * pmdslot;

        r = page_walk(vaoff, &upmd);
        ASSERT_MSG(r == 0, "page_walk");

        for (i = 0; i < phnum; i++, phdr++) {
                uint64_t va, end_fileva, end_memva;

                if (phdr->p_type != PT_LOAD)
                        continue;

                va = phdr->p_vaddr + *basep;

                if (pudidx == -1)
                        pudidx = pdpt_index(va);

                end_fileva = va + phdr->p_filesz;
                end_memva = va + phdr->p_memsz;
                ASSERT_MSG(pudidx == pdpt_index(va), "must fit within one pmd");
                ASSERT_MSG(pdpt_index(va) == pdpt_index(end_memva), "must fit within one pmd");
                ASSERT_MSG(end_fileva <= end_memva, "file size must be no larger than memory size");
                ASSERT_MSG(end_memva >= va, "must not overflow in elf");
                ASSERT_MSG(end_memva < UINT64_C(0x800000000000), "must be in lower half");

                map_pages(rounddown(va + vaoff, SZ_2M), end_memva - rounddown(va, SZ_2M), PTE_PRESENT | PTE_USER | PTE_RW | PTE_PSE);
                n = 0;
                while (n < phdr->p_filesz) {
                        ni = pread(fd, (void *)va + vaoff + n, phdr->p_filesz - n, phdr->p_offset + n);
                        ASSERT_MSG(ni >= 0, "pread");
                        n += ni;
                }
                ASSERT_MSG(n == phdr->p_filesz, "pread");
        }

        // TODO.. labels
        struct label secrecy, integrity;
        self_get_label(&secrecy, &integrity, NULL);

        r = alloc_directory_pud(upud, self_get_internal_container(), &secrecy, &integrity, name);
        ASSERT_MSG(r == 0, "alloc_directory_pud");
        r = directory_link_pmd(*upud, pudidx, upmd);
        ASSERT_MSG(r == 0, "sys_directory_link_pmd");

        /* close the elf file before copying the file table */
        close(fd);

        // copy the file table over and map any open file
        ASSERT_MSG(FS_FILE_STRUCT_END - FS_FILE_STRUCT_START <= SZ_2M, "FIXME");
        map_pages((uintptr_t)FS_FILE_STRUCT_START + vaoff, SZ_2M,
                  PTE_PRESENT | PTE_USER | PTE_RW | PTE_PSE);
        memcpy((void *)FS_FILE_STRUCT_START + vaoff, (void *)FS_FILE_STRUCT_START, SZ_2M);

        uintptr_t fs_map = FS_FILE_MAP_START;
        while (fs_map < FS_FILE_MAP_END) {
                usymlink_t sym;
                if (directory_get_slot(pud, pdpt_index(fs_map), &sym) == 0)
                        directory_link_pmd(*upud, pdpt_index(fs_map), sym);
                fs_map += SZ_1G;
        }

        /* unmap the temporary elf mappings */
        r = directory_unlink_pmd(pud, pmdslot);
        ASSERT_MSG(r == 0, "directory_unlink");

        return (void *)(*basep + ehdr->e_entry);
}
