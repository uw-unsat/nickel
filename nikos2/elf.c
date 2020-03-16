#include <io/cpio.h>
#include <io/elf.h>
#include <sys/errno.h>
#include <sys/multiboot.h>
#include <sys/string.h>
#include "elf.h"
#include "proc.h"
#include "vm.h"

static uintptr_t elf_entry[NR_ELF_FILES];
static uint8_t elf_data[NR_ELF_FILES][SZ_2M];
static const char *filenames[] = {
        [ELF_FILE_IDLE]         = "idle",
        [ELF_FILE_ALICE]        = "alice",
        [ELF_FILE_BOB]          = "bob",
        [ELF_FILE_HACKER]       = "hacker",
};

static void elf_copy(size_t fileid, const char *name, void *start, size_t size)
{
        struct cpio_data cd = find_cpio_data(name, start, size, NULL);
        struct elf64_hdr *hdr = cd.data;
        struct elf64_phdr *phdr;
        size_t i, n;

        pr_info("elf: file %zu \"%s\"\n", fileid, name);
        BUG_ON(memcmp(hdr->e_ident, ELFMAG, SELFMAG));

        elf_entry[fileid] = hdr->e_entry;

        phdr = (void *)hdr + hdr->e_phoff;
        n = hdr->e_phnum;
        for (i = 0; i < n; ++i, ++phdr) {
                uintptr_t va;
                size_t filesz, memsz;
                void *src, *dst;

                if (phdr->p_type != PT_LOAD)
                        continue;
                va = phdr->p_vaddr;
                filesz = phdr->p_filesz;
                memsz = phdr->p_memsz;
                BUG_ON(filesz > memsz);
                BUG_ON(va + memsz < va);
                if (filesz == 0)
                        continue;
                src = (void *)hdr + phdr->p_offset;
                /* assume user code/data fits */
                BUG_ON(va < ELF_VA_SLOT * SZ_2M);
                BUG_ON(va + filesz >= (ELF_VA_SLOT + 1) * SZ_2M);
                dst = elf_data[fileid] + va % SZ_2M;
                memcpy(dst, src, filesz);
        }
}

void elf_init(struct multiboot_info *info)
{
        struct multiboot_mod_list *mod;
        void *start;
        size_t size, i;

        BUG_ON(!(info->flags & MULTIBOOT_INFO_MODS));
        BUG_ON(!info->mods_count);
        mod = __va(info->mods_addr);
        start = __va(mod->mod_start);
        size = mod->mod_end - mod->mod_start;

        for (i = 0; i < ARRAY_SIZE(filenames); ++i)
                elf_copy(i, filenames[i], start, size);
}

uintptr_t elf_get_entry(size_t fileid)
{
        BUG_ON(fileid >= NR_ELF_FILES);
        return elf_entry[fileid];
}

void *elf_get_data(size_t fileid)
{
        BUG_ON(fileid >= NR_ELF_FILES);
        return elf_data[fileid];
}
