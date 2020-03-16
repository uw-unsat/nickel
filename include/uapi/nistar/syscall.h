#pragma once

#include <nistar/types.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#define USYMLINK_INVALID ((usymlink_t) { .upage = 0, .uparent = 0, .uparent_slot = 0 })

typedef unsigned __int128 upage_id_t;
typedef uint64_t quantum_id_t;

typedef struct {
        upage_id_t upage;
        /* parent container */
        upage_id_t uparent;
        /* cache the slot entry.. this goes away when we
           remove slots from the syscall interface */
        size_t  uparent_slot;
} usymlink_t;

static inline usymlink_t __usymlink(upage_id_t uobj, upage_id_t uparent)
{
        return (usymlink_t) {
                .upage = uobj,
                .uparent = uparent,
                .uparent_slot = 0,
        };
}

static inline bool usymlink_eq(usymlink_t a, usymlink_t b)
{
        return a.upage == b.upage &&
               a.uparent == b.uparent &&
               a.uparent_slot == b.uparent_slot;
}

static inline bool usymlink_is_valid(usymlink_t usym)
{
        return usym.upage != USYMLINK_INVALID.upage;
}

typedef unsigned __int128  tag_t;

long sys_container_get_root(upage_id_t *ucon);
long sys_container_get_slot(upage_id_t ucon, size_t slot, upage_id_t *to);
long sys_container_get_quota(upage_id_t ucon, size_t *quota);
long sys_container_get_uquota(upage_id_t ucon, size_t *quota);
long sys_container_get_qquota(upage_id_t ucon, size_t *quota);
long sys_container_move_quota(upage_id_t from, upage_id_t to);
long sys_container_move_uquota(upage_id_t from, upage_id_t to);
long sys_container_move_qquota(upage_id_t from, quantum_id_t qid, upage_id_t to);
long sys_container_get_parent(upage_id_t ucon, upage_id_t *parent);

long sys_reserve_page(upage_id_t ucon, size_t slot);

long sys_alloc_quantum(upage_id_t ucon, quantum_id_t qid, upage_id_t uthread);
long sys_alloc_tag(size_t slot, tag_t *tag);
long sys_alloc_container(upage_id_t ucon, size_t slot, size_t sslot,
                size_t islot, const tag_t secrecy[LABEL_NR_TAGS], const tag_t integrity[LABEL_NR_TAGS]);
long sys_alloc_thread(upage_id_t ucon, size_t slot, size_t sslot, size_t islot, size_t oslot,
                const tag_t secrecy[LABEL_NR_TAGS], const tag_t integrity[LABEL_NR_TAGS],
                const tag_t ownership[LABEL_NR_TAGS], size_t tslot, usymlink_t gate);
long sys_alloc_gate(upage_id_t ucon, size_t slot, size_t
                sslot, size_t islot, size_t oslot, size_t gslot,
                const tag_t secrecy[LABEL_NR_TAGS], const tag_t integrity[LABEL_NR_TAGS],
                const tag_t ownership[LABEL_NR_TAGS], const tag_t
                guard[LABEL_NR_TAGS], usymlink_t pud, void *entry,
                uint64_t arg0, uint64_t arg1, uint64_t arg2);
long sys_alloc_block(upage_id_t ucon, size_t slot, size_t sslot,
                size_t islot, const tag_t secrecy[LABEL_NR_TAGS], const tag_t integrity[LABEL_NR_TAGS]);
long sys_alloc_directory_pud(upage_id_t ucon, size_t slot, size_t sslot,
                size_t islot, const tag_t secrecy[LABEL_NR_TAGS], const tag_t integrity[LABEL_NR_TAGS]);
long sys_alloc_directory_pmd(upage_id_t ucon, size_t slot, size_t sslot,
                size_t islot, const tag_t secrecy[LABEL_NR_TAGS], const tag_t integrity[LABEL_NR_TAGS]);

long sys_directory_get_slot(upage_id_t usym, size_t slot, usymlink_t *to);
long sys_directory_link_pmd(upage_id_t upud, size_t pudslot, upage_id_t ucon, size_t slot);
long sys_directory_link_block(upage_id_t upud, size_t pudslot, upage_id_t ucon, size_t slot, uint64_t perm);
long sys_directory_unlink_pmd(upage_id_t upud, size_t pudslot);
long sys_directory_unlink_block(upage_id_t upud, size_t pudslot);

long sys_free_gate(upage_id_t ucon, size_t slot);
long sys_free_block(upage_id_t ucon, size_t slot);
long sys_free_directory_pud(upage_id_t ucon, size_t slot);
long sys_free_directory_pmd(upage_id_t ucon, size_t slot);
long sys_free_thread(upage_id_t ucon, size_t slot);
long sys_free_container(upage_id_t ucon, size_t slot);

long sys_page_get_type(upage_id_t ucon, size_t slot, uint64_t *to);
long sys_page_get_label(upage_id_t ucon, size_t slot, tag_t secrecy[LABEL_NR_TAGS], tag_t integrity[LABEL_NR_TAGS]);
long sys_page_get_name(upage_id_t ucon, size_t slot, char name[PAGE_NAME_LEN]);
long sys_page_set_name(upage_id_t ucon, size_t slot, const char name[PAGE_NAME_LEN]);
long sys_page_get_metadata(upage_id_t ucon, size_t slot, char metadata[PAGE_METADATA_LEN]);
long sys_page_set_metadata(upage_id_t ucon, size_t slot, const char metadata[PAGE_METADATA_LEN]);

long sys_gate_call(upage_id_t ucon, size_t slot, const tag_t ownership[LABEL_NR_TAGS], uintptr_t arg,
                   upage_id_t ret_con, size_t ret_slot, const tag_t ret_ownership[LABEL_NR_TAGS]);
long sys_gate_enter(upage_id_t ucon, size_t slot, const tag_t ownership[LABEL_NR_TAGS], uintptr_t arg, uintptr_t rsp);
long sys_gate_get_label(upage_id_t ucon, size_t slot, tag_t secrecy[LABEL_NR_TAGS], tag_t integrity[LABEL_NR_TAGS], tag_t ownership[LABEL_NR_TAGS]);

long sys_thread_get_state(upage_id_t ucon, size_t slot);

long sys_self_get(usymlink_t *uself);
long sys_self_get_pud(usymlink_t *ucon);
long sys_self_get_label(tag_t secrecy[LABEL_NR_TAGS], tag_t integrity[LABEL_NR_TAGS], tag_t ownership[LABEL_NR_TAGS]);
long sys_self_set_label(tag_t secrecy[LABEL_NR_TAGS], tag_t integrity[LABEL_NR_TAGS], tag_t ownership[LABEL_NR_TAGS]);

long sys_net_transmit(const char *ptr, size_t len, uint64_t *written);
long sys_net_receive(char *ptr, size_t len, uint64_t *read);

long sys_debug_print(const char *ptr);
long sys_debug_getchar(void);
long sys_debug_yield(void);
long sys_debug_self_halt(void);
long sys_debug_elapsed_quanta(void);
uint64_t sys_debug_uptime(void);
