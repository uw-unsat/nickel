#pragma once

#include <errno.h>
#include <nistar/assert.h>
#include <nistar/types.h>
#include <nistar/syscall.h>
#include <io/compiler.h>
#include <limits.h>
#include <stdbool.h>
#include <stdnoreturn.h>

#define TAG_INVALID ((unsigned __int128)(UINT64_MAX) << 64 | UINT64_MAX)

extern usymlink_t current_internal_container;

/* labels */
struct label {
        tag_t tags[LABEL_NR_TAGS];
};

void label_init(struct label *la);
long label_add_tag(struct label *la, tag_t tag);
long label_remove_tag(struct label *la, tag_t tag);
void label_copy(struct label *la, struct label *lb);
long label_union(struct label *la, struct label *lb);
long label_intersection(struct label *la, struct label *lb);
long label_subtract(struct label *la, struct label *lb);
bool label_is_subset(struct label *la, struct label *lb);
bool label_is_subsetx(struct label *la, struct label *lb, struct label *lx);
void label_format(struct label *la, char *buf, size_t size);

ssize_t find_free_directory_slot(usymlink_t udir);

/* container */
long container_get_slot(usymlink_t cont, size_t slot, usymlink_t *obj);
long container_find_by_name(usymlink_t cont, const char *name, usymlink_t *res);
usymlink_t container_get_root(void);
long container_get_quota(usymlink_t ucon, uint64_t *quota);
long container_get_uquota(usymlink_t ucon, uint64_t *quota);
long container_get_qquota(usymlink_t ucon, uint64_t *quota);
long container_move_quota(usymlink_t c1, usymlink_t c2, size_t amount);
long container_move_uquota(usymlink_t c1, usymlink_t c2, size_t amount);
long container_move_qquota(usymlink_t c1, usymlink_t c2, size_t amount);

long reserve_page(usymlink_t *page, usymlink_t ucon);

/* thread */
long thread_get_state(usymlink_t thread);

/* self */
usymlink_t self_get();
usymlink_t self_get_pud();
long self_get_label(struct label *secrecy, struct label *integrity, struct label *ownership);
long self_set_label(struct label *secrecy, struct label *integrity, struct label *ownership);

/* page */
long page_get_container(usymlink_t usym, usymlink_t *parent);
long page_get_type(usymlink_t usym, uint64_t *type);
long page_get_name(usymlink_t usym, char name[PAGE_NAME_LEN]);
long page_set_name(usymlink_t usym, const char name[PAGE_NAME_LEN]);
long page_get_metadata(usymlink_t usym, char metadata[PAGE_METADATA_LEN]);
long page_set_metadata(usymlink_t usym, const char metadata[PAGE_METADATA_LEN]);
long page_get_label(usymlink_t usym, struct label *la_secrecy, struct label *la_integrity);

long alloc_quantum(usymlink_t ucon, usymlink_t thread);
long alloc_quanta(usymlink_t ucon, usymlink_t thread, size_t amount);

tag_t alloc_tag();

long alloc_thread(usymlink_t *thread, usymlink_t ucon, struct label *secrecy,
                  struct label *integrity, struct label *ownership, usymlink_t gate, const char *name);

/* gate */
long alloc_gate(usymlink_t *ugte, usymlink_t ucon, struct label *secrecy, struct label *integrity,
                struct label *ownership, struct label *guard, usymlink_t pud, void *entry,
                uint64_t arg0, uint64_t arg1, uint64_t arg2, const char *name);

long gate_enter(usymlink_t ugte, struct label *ownership, uintptr_t arg, uintptr_t rsp);
long gate_call(usymlink_t ugte, usymlink_t alloc_container, uintptr_t arg);
long gate_get_label(usymlink_t usym, struct label *la_secrecy, struct label *la_integrity, struct label *la_ownership);

long alloc_call_gate(usymlink_t *ugte, usymlink_t ucont, struct label *secrecy, struct label *integrity,
                     struct label *ownership, struct label *guard, usymlink_t pud, void *entry, uint64_t arg1, const char *name);
long alloc_container(usymlink_t *ucont, usymlink_t parent, struct label *secrecy, struct label *integrity, char *name);

long alloc_directory_pud(usymlink_t *pud, usymlink_t ucont, struct label *secrecy, struct label *integrity, char *name);
long alloc_directory_pmd(usymlink_t *pmd, usymlink_t ucont, struct label *secrecy, struct label *integrity, char *name);
long alloc_block(usymlink_t *blk, usymlink_t ucont, struct label *secrecy, struct label *integrity, const char *name);

/* directory */
long directory_get_slot(usymlink_t upud, size_t idx, usymlink_t *usym);
long directory_link_pmd(usymlink_t upud, size_t idx, usymlink_t upmd);
long directory_link_block(usymlink_t upmd, size_t idx, usymlink_t block, pteval_t perm);
long directory_unlink_pmd(usymlink_t upud, size_t idx);
long directory_unlink_block(usymlink_t upmd, size_t idx);

/* free */
long free_page(usymlink_t usym);
long free_page_recursive(usymlink_t usym);
long free_gate(usymlink_t usym);
long free_block(usymlink_t usym);
long free_directory_pud(usymlink_t usym);
long free_directory_pmd(usymlink_t usym);
long free_thread(usymlink_t usym);
long free_container(usymlink_t usym);

/* mm */
long alloc_internal_block(usymlink_t *sym);
long page_walk(uintptr_t va, usymlink_t *pmd);
long map_pages(uintptr_t va, size_t n, pteval_t perm);
long unmap_pages(uintptr_t va, size_t len);
uintptr_t hs_brk(uintptr_t newbrk);
void *map_block(uintptr_t va, usymlink_t block, pteval_t perm);
long unmap_block(uintptr_t va);

/* network */
long net_transmit(const void *ptr, size_t len);
long net_receive(void *ptr, size_t len);

/* debugging */
void debug_printf(const char *fmt, ...) __printf(1, 2);
void debug_print_label(struct label *la);
void debug_print_container(usymlink_t ucon);
void debug_print_container_recursive(usymlink_t ucon);
void debug_print_directory(usymlink_t udir);
void debug_print_directory_recursive(usymlink_t udir);
void debug_print_usym(usymlink_t ucon);
