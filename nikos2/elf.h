#pragma once

#include <sys/multiboot.h>
#include <uapi/mcertikos/elf.h>

/* assume elf code/data fits in [4M, 6M) */
#define ELF_VA_SLOT     2

void elf_init(struct multiboot_info *info);
uintptr_t elf_get_entry(size_t fielid);
void *elf_get_data(size_t fileid);
