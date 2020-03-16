#include <elf.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <link.h>
#include <setjmp.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>
#include "internal/atomic.h"
#include "internal/dynlink.h"
#include "internal/libc.h"
#include "nistar/ulib.h"

#if 0
static void error(const char *, ...);
#else
#define error debug_printf
#endif

struct dso {
        unsigned char *base;
        char *name;
        size_t *dynv;
        struct dso *next, *prev;

        Phdr *phdr;
        int phnum;
        size_t phentsize;
        Sym *syms;
        Elf_Symndx *hashtab;
        uint32_t *ghashtab;
        int16_t *versym;
        char *strings;
        struct dso *syms_next, *lazy_next;
        size_t *lazy, lazy_cnt;
        unsigned char *map;
        size_t map_len;
        char relocated;
        char constructed;
        char kernel_mapped;
        char *rpath_orig, *rpath;

        size_t relro_start, relro_end;
        char *shortname;
        struct funcdesc {
                void *addr;
                size_t *got;
        } *funcdescs;
        size_t *got;
        char buf[];
};

struct symdef {
        Sym *sym;
        struct dso *dso;
};

__attribute__((__visibility__("hidden")))
const char *__libc_get_version(void);

#define ADDEND_LIMIT 4096
static size_t *saved_addends, *apply_addends_to;

static struct dso ldso;
static struct dso *head;
static char *env_path;
static int runtime;
static int ldd_mode;
static jmp_buf *rtld_fail;

#define weak_alias(old, new) \
        extern __typeof(old) new __attribute__((weak, alias(#old)))

__attribute__((__visibility__("hidden")))
void (*const __init_array_start)(void)=0, (*const __fini_array_start)(void)=0;

__attribute__((__visibility__("hidden")))
extern void (*const __init_array_end)(void), (*const __fini_array_end)(void);

weak_alias(__init_array_start, __init_array_end);
weak_alias(__fini_array_start, __fini_array_end);


/* Compute load address for a virtual address in a given dso. */
#define laddr(p, v)     (void *)((p)->base + (v))
#define fpaddr(p, v)    ((void (*)())laddr(p, v))

static void decode_vec(size_t *v, size_t *a, size_t cnt)
{
        size_t i;
        for (i=0; i<cnt; i++) a[i] = 0;
        for (; v[0]; v+=2) if (v[0]-1<cnt-1) {
                a[0] |= 1UL<<v[0];
                a[v[0]] = v[1];
        }
}

static int search_vec(size_t *v, size_t *r, size_t key)
{
        for (; v[0]!=key; v+=2)
                if (!v[0]) return 0;
        *r = v[1];
        return 1;
}

static uint32_t sysv_hash(const char *s0)
{
        const unsigned char *s = (void *)s0;
        uint_fast32_t h = 0;
        while (*s) {
                h = 16*h + *s++;
                h ^= h>>24 & 0xf0;
        }
        return h & 0xfffffff;
}

static uint32_t gnu_hash(const char *s0)
{
        const unsigned char *s = (void *)s0;
        uint_fast32_t h = 5381;
        for (; *s; s++)
                h += h*32 + *s;
        return h;
}

static Sym *sysv_lookup(const char *s, uint32_t h, struct dso *dso)
{
        size_t i;
        Sym *syms = dso->syms;
        Elf_Symndx *hashtab = dso->hashtab;
        char *strings = dso->strings;
        for (i=hashtab[2+h%hashtab[0]]; i; i=hashtab[2+hashtab[0]+i]) {
                if ((!dso->versym || dso->versym[i] >= 0)
                    && (!strcmp(s, strings+syms[i].st_name)))
                        return syms+i;
        }
        return 0;
}

static Sym *gnu_lookup(uint32_t h1, uint32_t *hashtab, struct dso *dso, const char *s)
{
        uint32_t nbuckets = hashtab[0];
        uint32_t *buckets = hashtab + 4 + hashtab[2]*(sizeof(size_t)/4);
        uint32_t i = buckets[h1 % nbuckets];

        if (!i) return 0;

        uint32_t *hashval = buckets + nbuckets + (i - hashtab[1]);

        for (h1 |= 1; ; i++) {
                uint32_t h2 = *hashval++;
                if ((h1 == (h2|1)) && (!dso->versym || dso->versym[i] >= 0)
                    && !strcmp(s, dso->strings + dso->syms[i].st_name))
                        return dso->syms+i;
                if (h2 & 1) break;
        }

        return 0;
}

static Sym *gnu_lookup_filtered(uint32_t h1, uint32_t *hashtab, struct dso *dso, const char *s, uint32_t fofs, size_t fmask)
{
        const size_t *bloomwords = (const void *)(hashtab+4);
        size_t f = bloomwords[fofs & (hashtab[2]-1)];
        if (!(f & fmask)) return 0;

        f >>= (h1 >> hashtab[3]) % (8 * sizeof f);
        if (!(f & 1)) return 0;

        return gnu_lookup(h1, hashtab, dso, s);
}

#define OK_TYPES (1<<STT_NOTYPE | 1<<STT_OBJECT | 1<<STT_FUNC | 1<<STT_COMMON | 1<<STT_TLS)
#define OK_BINDS (1<<STB_GLOBAL | 1<<STB_WEAK | 1<<STB_GNU_UNIQUE)

#ifndef ARCH_SYM_REJECT_UND
#define ARCH_SYM_REJECT_UND(s) 0
#endif

static struct symdef find_sym(struct dso *dso, const char *s, int need_def)
{
        uint32_t h = 0, gh = gnu_hash(s), gho = gh / (8*sizeof(size_t)), *ght;
        size_t ghm = 1ul << gh % (8*sizeof(size_t));
        struct symdef def = {0};
        for (; dso; dso=dso->syms_next) {
                Sym *sym;
                if ((ght = dso->ghashtab)) {
                        sym = gnu_lookup_filtered(gh, ght, dso, s, gho, ghm);
                } else {
                        if (!h) h = sysv_hash(s);
                        sym = sysv_lookup(s, h, dso);
                }
                if (!sym) continue;
                if (!sym->st_shndx)
                        if (need_def || (sym->st_info&0xf) == STT_TLS
                            || ARCH_SYM_REJECT_UND(sym))
                                continue;
                if (!sym->st_value)
                        if ((sym->st_info&0xf) != STT_TLS)
                                continue;
                if (!(1<<(sym->st_info&0xf) & OK_TYPES)) continue;
                if (!(1<<(sym->st_info>>4) & OK_BINDS)) continue;
                def.sym = sym;
                def.dso = dso;
                break;
        }
        return def;
}

static void do_relocs(struct dso *dso, size_t *rel, size_t rel_size, size_t stride)
{
        unsigned char *base = dso->base;
        Sym *syms = dso->syms;
        char *strings = dso->strings;
        Sym *sym;
        const char *name;
        void *ctx;
        int type;
        int sym_index;
        struct symdef def;
        size_t *reloc_addr;
        size_t sym_val;
        size_t tls_val;
        size_t addend;
        int skip_relative = 0, reuse_addends = 0, save_slot = 0;

        if (dso == &ldso) {
                /* Only ldso's REL table needs addend saving/reuse. */
                if (rel == apply_addends_to)
                        reuse_addends = 1;
                skip_relative = 1;
        }

        for (; rel_size; rel+=stride, rel_size-=stride*sizeof(size_t)) {
                if (skip_relative && IS_RELATIVE(rel[1], dso->syms)) continue;
                type = R_TYPE(rel[1]);
                if (type == REL_NONE) continue;
                reloc_addr = laddr(dso, rel[0]);

                if (stride > 2) {
                        addend = rel[2];
                } else if (type==REL_GOT || type==REL_PLT|| type==REL_COPY) {
                        addend = 0;
                } else if (reuse_addends) {
                        /* Save original addend in stage 2 where the dso
                         * chain consists of just ldso; otherwise read back
                         * saved addend since the inline one was clobbered. */
                        if (head==&ldso)
                                saved_addends[save_slot] = *reloc_addr;
                        addend = saved_addends[save_slot++];
                } else {
                        addend = *reloc_addr;
                }

                sym_index = R_SYM(rel[1]);
                if (sym_index) {
                        sym = syms + sym_index;
                        name = strings + sym->st_name;
                        ctx = type==REL_COPY ? head->syms_next : head;
                        def = (sym->st_info&0xf) == STT_SECTION
                                ? (struct symdef){ .dso = dso, .sym = sym }
                                : find_sym(ctx, name, type==REL_PLT);
                        if (!def.sym && (sym->st_shndx != SHN_UNDEF
                            || sym->st_info>>4 != STB_WEAK)) {
                                if (dso->lazy && (type==REL_PLT || type==REL_GOT)) {
                                        dso->lazy[3*dso->lazy_cnt+0] = rel[0];
                                        dso->lazy[3*dso->lazy_cnt+1] = rel[1];
                                        dso->lazy[3*dso->lazy_cnt+2] = addend;
                                        dso->lazy_cnt++;
                                        continue;
                                }
                                error("Error relocating %s: %s: symbol not found",
                                        dso->name, name);
                                if (runtime) longjmp(*rtld_fail, 1);
                                continue;
                        }
                } else {
                        sym = 0;
                        def.sym = 0;
                        def.dso = dso;
                }

                sym_val = def.sym ? (size_t)laddr(def.dso, def.sym->st_value) : 0;
                tls_val = def.sym ? def.sym->st_value : 0;

                switch (type) {
                case REL_NONE:
                        break;
                case REL_OFFSET:
                        addend -= (size_t)reloc_addr;
                case REL_SYMBOLIC:
                case REL_GOT:
                case REL_PLT:
                        *reloc_addr = sym_val + addend;
                        break;
                case REL_RELATIVE:
                        *reloc_addr = (size_t)base + addend;
                        break;
                case REL_SYM_OR_REL:
                        if (sym) *reloc_addr = sym_val + addend;
                        else *reloc_addr = (size_t)base + addend;
                        break;
                case REL_COPY:
                        memcpy(reloc_addr, (void *)sym_val, sym->st_size);
                        break;
                case REL_OFFSET32:
                        *(uint32_t *)reloc_addr = sym_val + addend
                                - (size_t)reloc_addr;
                        break;
                case REL_FUNCDESC:
                        *reloc_addr = def.sym ? (size_t)(def.dso->funcdescs
                                + (def.sym - def.dso->syms)) : 0;
                        break;
                case REL_FUNCDESC_VAL:
                        if ((sym->st_info&0xf) == STT_SECTION) *reloc_addr += sym_val;
                        else *reloc_addr = sym_val;
                        reloc_addr[1] = def.sym ? (size_t)def.dso->got : 0;
                        break;
                default:
                        error("Error relocating %s: unsupported relocation type %d",
                                dso->name, type);
                        if (runtime) longjmp(*rtld_fail, 1);
                        continue;
                }
        }
}

static void reloc_all(struct dso *p)
{
        size_t dyn[DYN_CNT];
        for (; p; p=p->next) {
                if (p->relocated) continue;
                decode_vec(p->dynv, dyn, DYN_CNT);
                do_relocs(p, laddr(p, dyn[DT_JMPREL]), dyn[DT_PLTRELSZ],
                        2+(dyn[DT_PLTREL]==DT_RELA));
                do_relocs(p, laddr(p, dyn[DT_REL]), dyn[DT_RELSZ], 2);
                do_relocs(p, laddr(p, dyn[DT_RELA]), dyn[DT_RELASZ], 3);

                if (head != &ldso && p->relro_start != p->relro_end &&
                    mprotect(laddr(p, p->relro_start), p->relro_end-p->relro_start, PROT_READ)
                    && errno != ENOSYS) {
                        error("Error relocating %s: RELRO protection failed: %m",
                                p->name);
                        if (runtime) longjmp(*rtld_fail, 1);
                }

                p->relocated = 1;
        }
}

static void kernel_mapped_dso(struct dso *p)
{
        size_t min_addr = -1, max_addr = 0, cnt;
        Phdr *ph = p->phdr;
        for (cnt = p->phnum; cnt--; ph = (void *)((char *)ph + p->phentsize)) {
                if (ph->p_type == PT_DYNAMIC) {
                        p->dynv = laddr(p, ph->p_vaddr);
                } else if (ph->p_type == PT_GNU_RELRO) {
                        p->relro_start = ph->p_vaddr & -PAGE_SIZE;
                        p->relro_end = (ph->p_vaddr + ph->p_memsz) & -PAGE_SIZE;
                }
                if (ph->p_type != PT_LOAD) continue;
                if (ph->p_vaddr < min_addr)
                        min_addr = ph->p_vaddr;
                if (ph->p_vaddr+ph->p_memsz > max_addr)
                        max_addr = ph->p_vaddr+ph->p_memsz;
        }
        min_addr &= -PAGE_SIZE;
        max_addr = (max_addr + PAGE_SIZE-1) & -PAGE_SIZE;
        p->map = p->base + min_addr;
        p->map_len = max_addr - min_addr;
        p->kernel_mapped = 1;
}

static void decode_dyn(struct dso *p)
{
        size_t dyn[DYN_CNT];
        decode_vec(p->dynv, dyn, DYN_CNT);
        p->syms = laddr(p, dyn[DT_SYMTAB]);
        p->strings = laddr(p, dyn[DT_STRTAB]);
        if (dyn[0]&(1<<DT_HASH))
                p->hashtab = laddr(p, dyn[DT_HASH]);
        if (dyn[0]&(1<<DT_RPATH))
                p->rpath_orig = p->strings + dyn[DT_RPATH];
        if (dyn[0]&(1<<DT_RUNPATH))
                p->rpath_orig = p->strings + dyn[DT_RUNPATH];
        if (dyn[0]&(1<<DT_PLTGOT))
                p->got = laddr(p, dyn[DT_PLTGOT]);
        if (search_vec(p->dynv, dyn, DT_GNU_HASH))
                p->ghashtab = laddr(p, *dyn);
        if (search_vec(p->dynv, dyn, DT_VERSYM))
                p->versym = laddr(p, *dyn);
}

/*
 * Stage 2 of the dynamic linker is called after relative relocations 
 * have been processed. It can make function calls to static functions
 * and access string literals and static data, but cannot use extern
 * symbols. Its job is to perform symbolic relocations on the dynamic
 * linker itself, but some of the relocations performed may need to be
 * replaced later due to copy relocations in the main program.
 */
__attribute__((__visibility__("hidden")))
void __dls2(unsigned char *base, size_t *sp)
{
        ldso.base = base;

        Ehdr *ehdr = (void *)ldso.base;
        ldso.name = ldso.shortname = "libc.so";
        ldso.phnum = ehdr->e_phnum;
        ldso.phdr = laddr(&ldso, ehdr->e_phoff);
        ldso.phentsize = ehdr->e_phentsize;
        kernel_mapped_dso(&ldso);
        decode_dyn(&ldso);

        /* Prepare storage for to save clobbered REL addends so they
         * can be reused in stage 3. There should be very few. If
         * something goes wrong and there are a huge number, abort
         * instead of risking stack overflow. */
        size_t dyn[DYN_CNT];
        decode_vec(ldso.dynv, dyn, DYN_CNT);
        size_t *rel = laddr(&ldso, dyn[DT_REL]);
        size_t rel_size = dyn[DT_RELSZ];
        size_t symbolic_rel_cnt = 0;
        apply_addends_to = rel;
        for (; rel_size; rel+=2, rel_size-=2*sizeof(size_t))
                if (!IS_RELATIVE(rel[1], ldso.syms)) symbolic_rel_cnt++;
        if (symbolic_rel_cnt >= ADDEND_LIMIT) a_crash();
        size_t addends[symbolic_rel_cnt+1];
        saved_addends = addends;

        head = &ldso;
        reloc_all(&ldso);

        ldso.relocated = 0;

        /* Call dynamic linker stage-3, __dls3, looking it up
         * symbolically as a barrier against moving the address
         * load across the above relocation processing. */
        struct symdef dls3_def = find_sym(&ldso, "__dls3", 0);
        ((stage3_func)laddr(&ldso, dls3_def.sym->st_value))(sp);
}

/*
 * Stage 3 of the dynamic linker is called with the dynamic linker/libc
 * fully functional. Its job is to load (if not already loaded) and
 * process dependencies and relocations for the main application and
 * transfer control to its entry point.
 */
void __dls3(size_t *sp)
{
        size_t aux[AUX_CNT], *auxv;
        size_t i;
        char *env_preload = NULL;
        char *replace_argv0 = NULL;
        int argc = *sp;
        char **argv = (void *)(sp + 1);
        char **argv_orig = argv;
        char **envp = argv + argc + 1;

        /* Find aux vector just past environ[] and use it to initialize
         * global data that may be needed before we can make syscalls. */
        __environ = envp;
        for (i=argc+1; argv[i]; i++);
        libc.auxv = auxv = (void *)(argv+i+1);
        decode_vec(auxv, aux, AUX_CNT);
        __hwcap = aux[AT_HWCAP];
        libc.page_size = aux[AT_PAGESZ];
        libc.secure = ((aux[0]&0x7800)!=0x7800 || aux[AT_UID]!=aux[AT_EUID]
                || aux[AT_GID]!=aux[AT_EGID] || aux[AT_SECURE]);

        /* Only trust user/env if kernel says we're not suid/sgid */
        if (!libc.secure) {
                env_path = getenv("LD_LIBRARY_PATH");
                env_preload = getenv("LD_PRELOAD");
        }

       /* load the main executable file */
        {
                char *ldname = argv[0];
                size_t l = strlen(ldname);
                if (l >= 3 && !strcmp(ldname+l-3, "ldd")) ldd_mode = 1;
                argv++;
                while (argv[0] && argv[0][0]=='-' && argv[0][1]=='-') {
                        char *opt = argv[0]+2;
                        *argv++ = (void *)-1;
                        if (!*opt) {
                                break;
                        } else if (!memcmp(opt, "list", 5)) {
                                ldd_mode = 1;
                        } else if (!memcmp(opt, "library-path", 12)) {
                                if (opt[12]=='=') env_path = opt+13;
                                else if (opt[12]) *argv = 0;
                                else if (*argv) env_path = *argv++;
                        } else if (!memcmp(opt, "preload", 7)) {
                                if (opt[7]=='=') env_preload = opt+8;
                                else if (opt[7]) *argv = 0;
                                else if (*argv) env_preload = *argv++;
                        } else if (!memcmp(opt, "argv0", 5)) {
                                if (opt[5]=='=') replace_argv0 = opt+6;
                                else if (opt[5]) *argv = 0;
                                else if (*argv) replace_argv0 = *argv++;
                        } else {
                                argv[0] = 0;
                        }
                }
                argv[-1] = (void *)(argc - (argv-argv_orig));
                argv[-1] = (void *)(argc - (argv-argv_orig));
                if (!argv[0]) {
                        dprintf(2, "musl libc (" LDSO_ARCH ")\n"
                                "Version %s\n"
                                "Dynamic Program Loader\n"
                                "Usage: %s [options] [--] pathname%s\n",
                                __libc_get_version(), ldname,
                                ldd_mode ? "" : " [args]");
                        _exit(1);
                }
        }

        ASSERT_MSG(false, "TODO __dls3\n");
}
