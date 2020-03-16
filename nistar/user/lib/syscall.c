#include <string.h>
#include <nistar/syscall.h>

#define TLS_START       0x7fffffc00000
#define TLS_INDEX(ptr) ((((uintptr_t)(ptr)) - TLS_START) >> 3)

enum {
#define __SYSCALL(x) SYS_##x,
#include <nistar/syscall.inc>
#undef __SYSCALL
};

extern long __nistar_syscall(long sys_nr, ...);
extern long __sys_gate_enter(upage_id_t ucon, size_t slot, const uintptr_t ownership, uintptr_t arg, uintptr_t rsp);
extern long __sys_gate_call(upage_id_t ucon, size_t slot, const uintptr_t ownership, uintptr_t arg, uint64_t unused,
                            upage_id_t ret_con, size_t ret_slot, const uintptr_t ret_ownership);

struct sys_extra_args {
        size_t extra0;
        size_t extra1;
        size_t extra2;
        size_t extra3;
        size_t extra4;
        size_t extra5;
        size_t extra6;
        size_t extra7;
        size_t extra8;
        size_t extra9;
        size_t extra10;
};

long sys_container_get_root(upage_id_t *ucon)
{
        int r;
        upage_id_t sym = 0;
        r = __nistar_syscall(SYS_container_get_root, TLS_INDEX(&sym));
        *ucon = sym;
        return r;
}

long sys_container_get_slot(upage_id_t ucon, size_t slot, upage_id_t *to)
{
        int r;
        upage_id_t sym = 0;
        r = __nistar_syscall(SYS_container_get_slot, ucon, slot, TLS_INDEX(&sym));
        *to = sym;
        return r;
}

long sys_container_get_quota(upage_id_t ucont, size_t *quota)
{
        int r;
        size_t q;
        r = __nistar_syscall(SYS_container_get_quota, ucont, TLS_INDEX(&q));
        *quota = q;
        return r;
}

long sys_container_get_uquota(upage_id_t ucont, size_t *quota)
{
        int r;
        size_t q;
        r = __nistar_syscall(SYS_container_get_uquota, ucont, TLS_INDEX(&q));
        *quota = q;
        return r;
}

long sys_container_get_qquota(upage_id_t ucont, size_t *quota)
{
        return __nistar_syscall(SYS_container_get_qquota, ucont, TLS_INDEX(quota));
}

long sys_container_move_quota(upage_id_t from, upage_id_t to)
{
        return __nistar_syscall(SYS_container_move_quota, from, to);
}

long sys_container_move_uquota(upage_id_t from, upage_id_t to)
{
        return __nistar_syscall(SYS_container_move_uquota, from, to);
}

long sys_container_move_qquota(upage_id_t from, quantum_id_t qid, upage_id_t to)
{
        return __nistar_syscall(SYS_container_move_qquota, from, qid, to);
}

long sys_container_get_parent(upage_id_t ucon, upage_id_t *parent)
{
        return __nistar_syscall(SYS_container_get_parent, ucon, TLS_INDEX(parent));
}

long sys_reserve_page(upage_id_t ucon, size_t slot)
{
        return __nistar_syscall(SYS_reserve_page, ucon, slot);
}

long sys_alloc_quantum(upage_id_t ucon, quantum_id_t qid, upage_id_t uthread)
{
        return __nistar_syscall(SYS_alloc_quantum, ucon, qid, uthread);
}

long sys_alloc_tag(size_t slot, tag_t *tag)
{
        int r;
        tag_t t;
        r = __nistar_syscall(SYS_alloc_tag, slot, TLS_INDEX(&t));
        *tag = t;
        return r;
}

long sys_alloc_container(upage_id_t ucon, size_t slot, size_t sslot, size_t islot, const tag_t secrecy[LABEL_NR_TAGS], const tag_t integrity[LABEL_NR_TAGS])
{
        struct sys_extra_args rest = {
                .extra0 = TLS_INDEX(secrecy),
                .extra1 = TLS_INDEX(integrity),
        };

        return __nistar_syscall(SYS_alloc_container, ucon, slot, sslot, islot, TLS_INDEX(&rest));
}

long sys_alloc_thread(upage_id_t ucon, size_t slot, size_t sslot, size_t islot, size_t oslot,
                      const tag_t secrecy[LABEL_NR_TAGS], const tag_t integrity[LABEL_NR_TAGS],
                      const tag_t ownership[LABEL_NR_TAGS], size_t tslot, usymlink_t gate)
{
        struct sys_extra_args rest = {
                .extra0 = oslot,
                .extra1 = TLS_INDEX(secrecy),
                .extra2 = TLS_INDEX(integrity),
                .extra3 = TLS_INDEX(ownership),
                .extra4 = tslot,
                .extra5 = TLS_INDEX(&gate),
        };
        return __nistar_syscall(SYS_alloc_thread, ucon, slot, sslot, islot, TLS_INDEX(&rest));
}

long sys_alloc_gate(upage_id_t ucon, size_t slot, size_t sslot, size_t islot, size_t oslot, size_t gslot,
                    const tag_t secrecy[LABEL_NR_TAGS], const tag_t integrity[LABEL_NR_TAGS], const tag_t ownership[LABEL_NR_TAGS],
                    const tag_t guard[LABEL_NR_TAGS], usymlink_t pud, void *entry,
                    uint64_t arg0, uint64_t arg1, uint64_t arg2)
{
        struct sys_extra_args rest = {
                .extra0 = oslot,
                .extra1 = gslot,
                .extra2 = TLS_INDEX(secrecy),
                .extra3 = TLS_INDEX(integrity),
                .extra4 = TLS_INDEX(ownership),
                .extra5 = TLS_INDEX(guard),
                .extra6 = TLS_INDEX(&pud),
                .extra7 = (uint64_t)entry,
                .extra8 = (uint64_t)arg0,
                .extra9 = (uint64_t)arg1,
                .extra10 = (uint64_t)arg2,
        };
        return __nistar_syscall(SYS_alloc_gate, ucon, slot, sslot, islot, TLS_INDEX(&rest));
}

long sys_alloc_block(upage_id_t ucon, size_t slot, size_t sslot, size_t islot, const tag_t secrecy[LABEL_NR_TAGS], const tag_t integrity[LABEL_NR_TAGS])
{
        struct sys_extra_args rest = {
                .extra0 = TLS_INDEX(secrecy),
                .extra1 = TLS_INDEX(integrity),
        };
        return __nistar_syscall(SYS_alloc_block, ucon, slot, sslot, islot, TLS_INDEX(&rest));
}

long sys_alloc_directory_pud(upage_id_t ucon, size_t slot, size_t sslot, size_t islot, const tag_t secrecy[LABEL_NR_TAGS], const tag_t integrity[LABEL_NR_TAGS])
{
        struct sys_extra_args rest = {
                .extra0 = TLS_INDEX(secrecy),
                .extra1 = TLS_INDEX(integrity),
        };
        return __nistar_syscall(SYS_alloc_directory_pud, ucon, slot, sslot, islot, TLS_INDEX(&rest));
}

long sys_alloc_directory_pmd(upage_id_t ucon, size_t slot, size_t sslot, size_t islot, const tag_t secrecy[LABEL_NR_TAGS], const tag_t integrity[LABEL_NR_TAGS])
{
        struct sys_extra_args rest = {
                .extra0 = TLS_INDEX(secrecy),
                .extra1 = TLS_INDEX(integrity),
        };
        return __nistar_syscall(SYS_alloc_directory_pmd, ucon, slot, sslot, islot, TLS_INDEX(&rest));
}

long sys_directory_get_slot(upage_id_t usym, size_t slot, usymlink_t *to)
{
        return __nistar_syscall(SYS_directory_get_slot, usym, slot, TLS_INDEX(to));
}

long sys_directory_link_pmd(upage_id_t upud, size_t pudslot, upage_id_t ucon, size_t slot)
{
        return __nistar_syscall(SYS_directory_link_pmd, upud, pudslot, ucon, slot);
}

long sys_directory_link_block(upage_id_t upmd, size_t pmdslot, upage_id_t ucon, size_t slot, uint64_t perm)
{
        struct sys_extra_args rest = {
                .extra0 = slot,
                .extra1 = perm,
        };
        return __nistar_syscall(SYS_directory_link_block, upmd, pmdslot, ucon, TLS_INDEX(&rest));
}

long sys_directory_unlink_pmd(upage_id_t upud, size_t pudslot)
{
        return __nistar_syscall(SYS_directory_unlink_pmd, upud, pudslot);
}

long sys_directory_unlink_block(upage_id_t upmd, size_t pmdslot)
{
        return __nistar_syscall(SYS_directory_unlink_block, upmd, pmdslot);
}

long sys_free_gate(upage_id_t ucon, size_t slot)
{
        return __nistar_syscall(SYS_free_gate, ucon, slot);
}

long sys_free_block(upage_id_t ucon, size_t slot)
{
        return __nistar_syscall(SYS_free_block, ucon, slot);
}

long sys_free_directory_pud(upage_id_t ucon, size_t slot)
{
        return __nistar_syscall(SYS_free_directory_pud, ucon, slot);
}

long sys_free_directory_pmd(upage_id_t ucon, size_t slot)
{
        return __nistar_syscall(SYS_free_directory_pmd, ucon, slot);
}

long sys_free_thread(upage_id_t ucon, size_t slot)
{
        return __nistar_syscall(SYS_free_thread, ucon, slot);
}

long sys_free_container(upage_id_t ucon, size_t slot)
{
        return __nistar_syscall(SYS_free_container, ucon, slot);
}

long sys_page_get_type(upage_id_t ucon, size_t slot, uint64_t *to)
{
        int r;
        uint64_t type = 0;
        r  =__nistar_syscall(SYS_page_get_type, ucon, slot, TLS_INDEX(&type));
        *to = type;
        return r;
}

long sys_page_get_label(upage_id_t ucon, size_t slot, tag_t secrecy[LABEL_NR_TAGS], tag_t integrity[LABEL_NR_TAGS])
{
        return __nistar_syscall(SYS_page_get_label, ucon, slot, TLS_INDEX(secrecy), TLS_INDEX(integrity));
}

long sys_page_get_name(upage_id_t ucon, size_t slot, char name[PAGE_NAME_LEN])
{
        return __nistar_syscall(SYS_page_get_name, ucon, slot, TLS_INDEX(name));
}

long sys_page_set_name(upage_id_t ucon, size_t slot, const char name[PAGE_NAME_LEN])
{
        return __nistar_syscall(SYS_page_set_name, ucon, slot, TLS_INDEX(name));
}

long sys_page_get_metadata(upage_id_t ucon, size_t slot, char metadata[PAGE_METADATA_LEN])
{
        return __nistar_syscall(SYS_page_get_metadata, ucon, slot, TLS_INDEX(metadata));
}

long sys_page_set_metadata(upage_id_t ucon, size_t slot, const char metadata[PAGE_METADATA_LEN])
{
        return __nistar_syscall(SYS_page_set_metadata, ucon, slot, TLS_INDEX(metadata));
}

long sys_gate_enter(upage_id_t ucon, size_t slot, const tag_t ownership[LABEL_NR_TAGS], uintptr_t arg, uintptr_t rsp)
{
        return __sys_gate_enter(ucon, slot, TLS_INDEX(ownership), arg, rsp);
}

long sys_gate_get_label(upage_id_t ucon, size_t slot, tag_t secrecy[LABEL_NR_TAGS], tag_t integrity[LABEL_NR_TAGS], tag_t ownership[LABEL_NR_TAGS])
{
        return __nistar_syscall(SYS_gate_get_label, ucon, slot, TLS_INDEX(secrecy), TLS_INDEX(integrity), TLS_INDEX(ownership));
}


long sys_gate_call(upage_id_t ucon, size_t slot, const tag_t ownership[LABEL_NR_TAGS], uintptr_t arg,
                   upage_id_t ret_con, size_t ret_slot, const tag_t ret_ownership[LABEL_NR_TAGS])
{
        return __sys_gate_call(ucon, slot, TLS_INDEX(ownership), arg,
                               /* push ret args to the stack */ 0,
                               ret_con, ret_slot, TLS_INDEX(ret_ownership));
}

long sys_thread_get_state(upage_id_t ucon, size_t slot)
{
        long r, state;
        r = __nistar_syscall(SYS_thread_get_state, ucon, slot, TLS_INDEX(&state));
        if (r)
                return r;
        return state;
}

long sys_self_get(usymlink_t *uself)
{
        return __nistar_syscall(SYS_self_get, TLS_INDEX(uself));
}

long sys_self_get_pud(usymlink_t *upud)
{
        return __nistar_syscall(SYS_self_get_pud, TLS_INDEX(upud));
}

long sys_self_get_label(tag_t secrecy[LABEL_NR_TAGS], tag_t integrity[LABEL_NR_TAGS], tag_t ownership[LABEL_NR_TAGS])
{
        return __nistar_syscall(SYS_self_get_label, TLS_INDEX(secrecy), TLS_INDEX(integrity), TLS_INDEX(ownership));
}

long sys_self_set_label(tag_t secrecy[LABEL_NR_TAGS], tag_t integrity[LABEL_NR_TAGS], tag_t ownership[LABEL_NR_TAGS])
{
        return __nistar_syscall(SYS_self_set_label, TLS_INDEX(secrecy), TLS_INDEX(integrity), TLS_INDEX(ownership));
}

long sys_debug_print(const char *ptr)
{
        return __nistar_syscall(SYS_debug_print, TLS_INDEX(ptr), strlen(ptr));
}

long sys_debug_elapsed_quanta(void)
{
        return __nistar_syscall(SYS_debug_elapsed_quanta);
}

long sys_net_transmit(const char *ptr, size_t len, uint64_t *written)
{
        return __nistar_syscall(SYS_net_transmit, TLS_INDEX(ptr), len, TLS_INDEX(written));
}

long sys_net_receive(char *ptr, size_t len, uint64_t *read)
{
        return __nistar_syscall(SYS_net_receive, TLS_INDEX(ptr), len, TLS_INDEX(read));
}

long sys_debug_getchar(void)
{
        return __nistar_syscall(SYS_debug_getchar);
}

long sys_debug_yield(void)
{
        return __nistar_syscall(SYS_debug_yield);
}

long sys_debug_self_halt(void)
{
        return __nistar_syscall(SYS_debug_self_halt);
}

uint64_t sys_debug_uptime(void)
{
        return __nistar_syscall(SYS_debug_uptime);
}
