#include <asm/init.h>
#include <io/elf.h>
#include <sys/string.h>
#include "translate.h"

extern char _binary_enclave_start[], _binary_enclave_end[];
static void (*test_enclave)(uint32_t nr) = (void *)x86_insns;

static void load_elf_segment(uintptr_t va, size_t memsz, void *src, size_t filesz)
{
        /* bad elf */
        BUG_ON(memsz < filesz);

        pr_info("load va=0x%lx memsz=%zu filesz=%zu\n", va, memsz, filesz);
}

static void load_elf(void *data)
{
        struct elf64_hdr *hdr = data;
        struct elf64_phdr *phdr;
        size_t i, n;

        if (memcmp(hdr->e_ident, ELFMAG, SELFMAG))
                panic("incorrect ELF header\n");

        phdr = data + hdr->e_phoff;
        n = hdr->e_phnum;
        for (i = 0; i < n; ++i, ++phdr) {
                if (phdr->p_type != PT_LOAD)
                        continue;
                load_elf_segment(phdr->p_vaddr, phdr->p_memsz, data + phdr->p_offset, phdr->p_filesz);
        }
}

static void load_test_enclave(void)
{
        size_t i, j, n;

        n = translate_test_enclave();
        BUG_ON(!n);

        for (i = 0; i < n; ++i) {
                pr_info("%04zx: %08x =>", i * X86_INSN_LEN, arm_insns[i]);
                for (j = 0; j < X86_INSN_LEN; ++j)
                        pr_cont(" %02x", x86_insns[i][j]);
                pr_cont("\n");
        }

        /* this is enter an infinite loop for now due to int $80 in kernel mode */
        test_enclave(0);
        load_elf(_binary_enclave_start);
}

noreturn void main(void)
{
        uart8250_init();
        vgacon_init();

        cpu_init();
        tsc_init();

        trap_init();

        load_test_enclave();

        die();
};
