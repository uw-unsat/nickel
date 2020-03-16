#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <nistar/assert.h>
#include <nistar/libfs.h>
#include <nistar/types.h>
#include <nistar/env.h>
#include <nistar/ulib.h>
#include <io/cpio.h>
#include <io/sizes.h>
#include <libgen.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define check(a) {{ long ret = (a); if (ret) return ret; }}

/* static tag_t fs_integrity = TAG_INVALID; */

static int init_root_dir()
{
        extern void _init_fs(void);

        struct label secrecy;
        struct label integrity;
        usymlink_t fs_root, root_container = container_get_root();

        label_init(&secrecy);
        label_init(&integrity);

        /* label_add_tag(&integrity, fs_integrity); */

        check(alloc_container(&fs_root, root_container, &secrecy, &integrity, "/"));
        check(container_move_quota(root_container, fs_root, 1024));

        _init_fs();

        return 0;
}

static int init_fs_image(size_t slot, size_t pudslot)
{
        int fd;
        size_t i;
        char name[PAGE_NAME_LEN];
        char buf[PAGE_NAME_LEN];
        void *data = (void*)(pudslot * SZ_1G);
        long len, offset = 0;
        struct cpio_data cd;
        usymlink_t root_container = container_get_root();

        usymlink_t pud, fs_image_pmd;

        pud = self_get_pud();

        container_get_slot(root_container, slot, &fs_image_pmd);
        page_get_name(fs_image_pmd, name);
        ASSERT_MSG(strncmp(name, "fsimage", PAGE_NAME_LEN) == 0, "Could not find fsimage");

        check(directory_link_pmd(pud, pudslot, fs_image_pmd));

        len = *(size_t*)data;
        data += 8;

        while (1) {
                cd = find_cpio_data("", data, len, &offset);
                if (!cd.data)
                        break;
                if (cd.name[0] == 0)
                        break;

                data += offset;
                len -= offset;

                switch (cd.mode & 0170000) {
                case 0100000:
                        /* regular files */
                        break;
                case 0120000:
                        /* symbolic links */
                        break;
                default:
                        continue;
                }

                strlcpy(buf, cd.name, PAGE_NAME_LEN);
                hs_mkdir_p(dirname(buf), 0);
                fd = creat(cd.name, 0);
                ASSERT_MSG(fd >= 0, "Could not create file %s: %d\n", cd.name, fd);
                size_t n = 0;
                while (n < cd.size)
                        n += write(fd, cd.data + n, cd.size - n);
                close(fd);
        }

        check(directory_unlink_pmd(pud, pudslot));

        usymlink_t blk;
        for (i = 0; i < DIRECTORY_NR_ENTRIES; i++) {
                if (directory_get_slot(fs_image_pmd, i, &blk) != 0)
                        break;
                ASSERT_MSG(free_block(blk) == 0, "free_block");
        }
        free_directory_pmd(fs_image_pmd);

        return 0;
}

/* static int init_gates() */
/* { */
/*         struct label secrecy, integrity, ownership, guard; */
/*         label_init(&secrecy); */
/*         label_init(&integrity); */
/*         label_init(&ownership); */
/*         label_init(&guard); */
/*         label_add_tag(&ownership, fs_integrity); */
/*  */
/*         check(alloc_call_gate(root, 5, &secrecy, &integrity, &ownership, &guard, pud, &do_pwrite, "pwrite")); */
/*         check(alloc_call_gate(root, 7, &secrecy, &integrity, &ownership, &guard, pud, &do_mkdir, "mkdir")); */
/*         check(alloc_call_gate(root, 8, &secrecy, &integrity, &ownership, &guard, pud, &do_mknod, "mknod")); */
/*         return 0; */
/* } */

static int fs_init(void)
{
        // de-taint the initial fs state.
        struct label secrecy, integrity, ownership, s, i;
        self_get_label(&secrecy, &integrity, &ownership);
        label_copy(&s, &secrecy);
        label_copy(&i, &secrecy);
        label_subtract(&s, &ownership);
        label_subtract(&i, &ownership);
        self_set_label(&s, &i, &ownership);

        debug_printf("init: loading fs\n");
        /* fs_integrity = alloc_tag(); */
        check(init_root_dir());
        // TODO: search for an unused slot and unmap after loading..
        check(init_fs_image(5, 10));
        /* check(init_gates()); */

        // Create a public home directory
        mkdir("/home", 0);

        // Restore previous labels
        self_set_label(&secrecy, &integrity, &ownership);
        return 0;
}

/* Initialize proc / internal containers for init */
static void proc_init(void)
{
        // TODO: Init should move its objects (thread, pud, pmd, blocks)
        // to its internal container.
        // initialize init's proc and internal containers.
        long r;
        struct label secrecy, integrity, ownership;
        usymlink_t proc, internal;
        tag_t stag, itag;
        char name[PAGE_NAME_LEN];
        uint64_t qquota;

        stag = alloc_tag();
        itag = alloc_tag();

        self_get_label(&secrecy, &integrity, &ownership);

        self_set_env_containers(container_get_root(), container_get_root());

        label_add_tag(&integrity, itag);

        page_set_name(self_get(), "/bin/init");

        strlcpy(name, program_invocation_name, sizeof(name));
        strlcat(name, "-", sizeof(name));
        strlcat(name, "proc-container", sizeof(name));
        r = alloc_container(&proc, container_get_root(), &secrecy, &integrity, name);
        ASSERT_MSG(r == 0, "alloc_container");
        debug_printf("proc container\n");

        container_move_quota(container_get_root(), proc, 32);
        self_set_process_container(proc);

        label_add_tag(&secrecy, stag);

        strlcpy(name, program_invocation_name, sizeof(name));
        strlcat(name, "-", sizeof(name));
        strlcat(name, "internal-container", sizeof(name));
        r = alloc_container(&internal, proc, &secrecy, &integrity, name);
        ASSERT_MSG(r == 0, "alloc_container");

        container_move_quota(container_get_root(), internal, 4096);
        container_move_uquota(container_get_root(), internal, 480); // claim the remaining quota

        r = container_get_qquota(container_get_root(), &qquota);
        ASSERT_MSG(r == 0, "container_get_qquota");
        container_move_qquota(container_get_root(), internal, qquota); // claim all time quota

        self_set_internal_container(internal);

        self_set_label(&secrecy, &integrity, &ownership);
}

static int ns_init(void)
{
        // usymlink_t icont = self_get_internal_container();

        if (fork() == 0) {
                // container_move_qquota(icont, self_get_internal_container(), 3);
                // alloc_quanta(self_get_internal_container(), self_get(), 3);

                execl("/bin/ns", "/bin/ns", NULL);
        }

        return 0;
}

int main(int argc, char **argv)
{
        int r;
        char *cmdline;

        proc_init();

        r = fs_init();
        if (r)
                debug_printf("init: failed to initialize fs\n");

        ASSERT_MSG(open("/dev/tty", O_RDONLY) == 0, "stdin");
        ASSERT_MSG(open("/dev/tty", O_WRONLY) == 1, "stdout");
        ASSERT_MSG(open("/dev/tty", O_WRONLY) == 2, "stderr");

        ASSERT_MSG(argc == 2, "init: argc must be 2\n");
        cmdline = strchr(argv[1], ' ');
        if (cmdline)
                ++cmdline;

        if (cmdline && cmdline[0]) {
                debug_printf("init: exec \"%s\"\n", cmdline);
                execl("/bin/sh", "/bin/sh", "-c", cmdline, NULL);
        }

#if 0
        r = ns_init();
        if (r)
                debug_printf("init: failed to initialize ns\n");
#endif

        execl("/bin/authd", "/bin/authd", NULL);

        return 0;
}
