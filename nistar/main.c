#include <asm/apic.h>
#include <asm/init.h>
#include <asm/setup.h>
#include <io/cpio.h>
#include <io/elf.h>
#include <sys/pci.h>
#include <sys/percpu.h>
#include <sys/string.h>
#include <uapi/nistar/memlayout.h>
#include <uapi/nistar/config.h>
#include "block.h"
#include "container.h"
#include "directory.h"
#include "invariants.h"
#include "label.h"
#include "sched.h"
#include "thread.h"

#define INIT                    "init"

extern phys_addr_t initrd_start, initrd_end;
extern char cmdline[CMDLINE_SIZE];

static uintptr_t load_elf(void *data1, void *data2)
{
        struct cpio_data cd = find_cpio_data(INIT, __va(initrd_start), initrd_end - initrd_start, NULL);
        struct elf64_hdr *hdr = cd.data;
        struct elf64_phdr *phdr;
        size_t i, n;
        uintptr_t va;

        BUG_ON(!hdr);

        if (memcmp(hdr->e_ident, ELFMAG, SELFMAG))
                panic("incorrect ELF header\n");
        phdr = (void *)hdr + hdr->e_phoff;
        n = hdr->e_phnum;
        /* assume user/init fits in [4M, 8M) */
        for (i = 0; i < n; ++i, ++phdr) {
                if (phdr->p_type != PT_LOAD)
                        continue;
                va = phdr->p_vaddr;
                BUG_ON(va < SZ_4M);
                BUG_ON(va + phdr->p_memsz < SZ_4M);
                BUG_ON(va >= SZ_4M + SZ_4M);
                BUG_ON(va + phdr->p_memsz >= SZ_4M + SZ_4M);
                if (va < SZ_4M + SZ_2M) {
                        BUG_ON(va + phdr->p_memsz >= SZ_4M + SZ_2M);
                        memcpy(data1 + (va - SZ_4M), (void *)hdr + phdr->p_offset, phdr->p_filesz);
                } else
                        memcpy(data2 + (va - SZ_4M - SZ_2M), (void *)hdr + phdr->p_offset, phdr->p_filesz);

        }

        return hdr->e_entry;
}

static page_id_t boot_page_alloc(void)
{
        static size_t next = 0;
        page_id_t id;

        while (!page_is_type(__page_id(next), PAGE_TYPE_NONE))
                ++next;
        id = __page_id(next);
        ++next;
        return id;
}

static page2m_id_t boot_page2m_alloc(void)
{
        static size_t next = 0;
        page2m_id_t id;

        while (!page2m_is_free(__page2m_id(next)))
                ++next;
        id = __page2m_id(next);
        ++next;
        return id;
}

static void alloc_label(page_id_t id)
{
        long r;
        page_id_t secrecy, integrity;
        secrecy = boot_page_alloc();
        r = label_alloc(secrecy);
        BUG_ON(r);
        integrity = boot_page_alloc();
        r = label_alloc(integrity);
        BUG_ON(r);

        page_get(id)->secrecy = secrecy;
        page_get(id)->integrity = integrity;
}

static void load_fs(page_id_t pmd)
{
        int r;
        page_id_t fs_block;
        void *data;
        bool first = true;
        size_t n, blocklen, len = initrd_end - initrd_start;
        size_t pmdidx = 0;
        void *p = __va(initrd_start);

        while (len) {
                fs_block = boot_page_alloc();
                r = block_alloc(fs_block, boot_page2m_alloc());
                BUG_ON(r);
                alloc_label(fs_block);
                strscpy((char *)page_get(fs_block)->name, "fsimage-block", PAGE_NAME_LEN);
                r = container_put_page(root_container_id, 6 + pmdidx, fs_block);
                BUG_ON(r);
                r = directory_link(pmd, pmdidx++, __ksymlink(__kpage_id(fs_block), __kpage_id(root_container_id)), PTE_PRESENT | PTE_USER | PTE_PSE);
                BUG_ON(r);
                data = block_data(fs_block);
                blocklen = (size_t)SZ_2M;
                if (first) {
                        *(size_t*)data = len;
                        first = false;
                        data += 8;
                        blocklen -= 8;
                }
                BUG_ON(r);
                n = min(blocklen, len);
                memcpy(data, p, n);
                p += n;
                len -= n;
        }
}

/*
 * Initial stack as defined by the AMD64 ABI:
 *
 *   Argument count             %rsp            8 bytes
 *   Argument pointers          %rsp+8          argc*8 bytes
 *   0                          8+8*argc+%rsp   8 bytes
 *   Environment pointers                       8 bytes each
 *   0                                          8 bytes
 *   Auxiliary vector entries                   16 bytes each
 *   Null auxiliary vector entry                8 bytes
 *
 * For our init, it's (2, argv[0], argv[1], 0, 0, 0, "/init", cmdline)
 */
static void stack_init(struct thread *thread)
{
        uint64_t *rsp;
        size_t cmdline_len = strlen(cmdline) + 1;
        size_t len = 64 + roundup(cmdline_len, 16);

        thread->cpu.rsp = USER_STACK_TOP - len;

        rsp = block_data(thread->local) + PAGE2M_SIZE - USER_TLS_SIZE - len;
        rsp[0] = 2;     /* argc */
        rsp[1] = thread->cpu.rsp + 6 * 8;
        rsp[2] = thread->cpu.rsp + 7 * 8;
        rsp[3] = 0;     /* 0 */
        rsp[4] = 0;     /* envp */
        rsp[5] = 0;     /* null aux */

        BUILD_BUG_ON(sizeof(INIT) > 8);
        memcpy(&rsp[6], INIT, sizeof(INIT));
        memcpy(&rsp[7], cmdline, cmdline_len);
}

static void user_init(void)
{
        page_id_t meta_label, meta_id, root_id;
        struct page *meta_page;
        int r;

        meta_label = boot_page_alloc();
        meta_id = boot_page_alloc();
        root_id = boot_page_alloc();
        root_container_id = root_id;

        /* create a meta container to hold the root container */
        r = label_alloc(meta_label);
        BUG_ON(r);
        r = label_add(meta_label, 0, tag_alloc());
        BUG_ON(r);
        r = container_alloc(meta_id);
        BUG_ON(r);
        page_get(meta_id)->secrecy = meta_label;
        page_get(meta_id)->integrity = meta_label;
        meta_page = page_get(meta_id);
        meta_page->c_quota = 0;
        meta_page->c_uquota = 0;

        /* initialize root container */
        r = container_alloc(root_id);
        BUG_ON(r);
        alloc_label(root_id);
        r = container_put_page(meta_id, 0, root_id);
        BUG_ON(r);
        r = container_set_parent(root_id, root_id);
        BUG_ON(r);

        /* initialize init */
        page_id_t pud, pmd;
        pud = boot_page_alloc();
        pmd = boot_page_alloc();

        r = directory_alloc(pud, PAGE_TYPE_PUD);
        BUG_ON(r);
        strscpy((char *)page_get(pud)->name, "PUD", PAGE_NAME_LEN);
        alloc_label(pud);
        r = container_put_page(root_id, 0, pud);
        BUG_ON(r);

        r = directory_alloc(pmd, PAGE_TYPE_PMD);
        BUG_ON(r);
        alloc_label(pmd);
        r = container_put_page(root_id, 1, pmd);
        BUG_ON(r);
        r = directory_put(pud, 0, __ksymlink(__kpage_id(pmd), __kpage_id(root_container_id)));
        BUG_ON(r);

        page_id_t blk_id1, blk_id2, fs_id;
        blk_id1 = boot_page_alloc();
        blk_id2 = boot_page_alloc();
        fs_id = boot_page_alloc();

        r = block_alloc(blk_id1, __page2m_id(0));
        BUG_ON(r);
        r = block_alloc(blk_id2, boot_page2m_alloc());
        BUG_ON(r);
        r = directory_alloc(fs_id, PAGE_TYPE_PMD);
        BUG_ON(r);
        alloc_label(fs_id);
        r = container_put_page(root_id, 5, fs_id);
        BUG_ON(r);

        alloc_label(blk_id1);
        r = container_put_page(root_container_id, 2, blk_id1);
        BUG_ON(r);
        r = directory_link(pmd, 2, __ksymlink(__kpage_id(blk_id1), __kpage_id(root_container_id)), PTE_PRESENT | PTE_USER | PTE_PSE | PTE_RW);
        BUG_ON(r);
        alloc_label(blk_id2);
        r = container_put_page(root_container_id, 3, blk_id2);
        BUG_ON(r);
        r = directory_link(pmd, 3, __ksymlink(__kpage_id(blk_id2), __kpage_id(root_container_id)), PTE_PRESENT | PTE_USER | PTE_PSE | PTE_RW);
        BUG_ON(r);

        page_id_t thread_id;
        page_id_t tsecrecy, tintegrity, townership;
        page_id_t tls;
        thread_id = boot_page_alloc();
        tls = boot_page_alloc();
        r = block_alloc(tls, boot_page2m_alloc());
        BUG_ON(r);
        r = thread_alloc(thread_id);
        BUG_ON(r);
        thread_set_local(thread_id, tls);
        tsecrecy = boot_page_alloc();
        tintegrity = boot_page_alloc();
        townership = boot_page_alloc();
        r = label_alloc(tsecrecy);
        BUG_ON(r);
        page_get(thread_id)->secrecy = tsecrecy;
        page_get(thread_id)->integrity = tintegrity;
        r = label_alloc(tintegrity);
        BUG_ON(r);
        r = label_alloc(townership);
        BUG_ON(r);

        struct thread *thread = page_data(thread_id);
        thread->ownership = townership;
        thread->state = THREAD_STATE_RUNNABLE;
        thread->mm = __ksymlink(__kpage_id(pud), __kpage_id(root_container_id));
        thread->cpu.rip = load_elf(block_data(blk_id1), block_data(blk_id2));
        thread->fsbase = USER_TLS_START;
        stack_init(thread);
        r = container_put_page(root_container_id, 4, thread_id);
        BUG_ON(r);

        /* initial fs image */
        load_fs(fs_id);
        strscpy((char *)page_get(fs_id)->name, "fsimage", PAGE_NAME_LEN);

        // Initialize root container's quota rest of available pages
        vm_init(root_id);
        block_init(root_id);
        sched_init(root_id, thread_id, thread_id);

        BUG_ON(!check_invariants());

        sched_next();
}

noreturn void main(unsigned int magic, struct multiboot_info *multiboot_info)
{
        /* enable output first */
        uart8250_init();
        vgacon_init();
        kbd_init();

        cpu_init();

        /* require cpu */
        tsc_init();

        /* require cpu */
        trap_init();

        /* require trap */
        syscall_init();

        acpi_table_init();

        /* require acpi, cpu */
        apic_init();

        /* switch to x2apic if available */
        x2apic_init();

        /* require apic */
        lapic_timer_set_periodic(1000000);

        /* require cpu */
        fpu_init();

        /* require fpu */
        thread_check_xstate_size();

        multiboot_init(magic, multiboot_info);

        /* require cpu */
        mtrr_init();

        /* require acpi */
        //iommu_init();

        /* require iommu, mtrr */
        e1000_init();
        pci_init();

        usymlink_init();

        tag_init();

        user_init();

        die();
}
