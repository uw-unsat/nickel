import sys
import datatypes as dt
import nickel.prototype as p


def kpage(name, concat=False):
    return ('{} gen'.format(name), dt.uint64_t, {'concat': concat})


def i64(name):
    return (name, dt.uint64_t)


def tls():
    return i64('to')


def slot():
    return i64('slot')


def label(name, check=False):
    return (name, dt.FreshLabel, {'check': check})


def usymlink(name):
    return ('{} gen parent parent.gen'.format(name), dt.uint64_t)


full_prototypes = {
    'sys_container_get_root': [tls()],
    'sys_container_get_root64': [tls()],
    'sys_container_get_slot': [kpage('usym'), slot(), tls()],
    'sys_container_get_slot64': [i64('con'), slot(), tls()],
    'sys_container_get_quota': [kpage('ucon'), tls()],
    'sys_container_get_uquota': [kpage('ucon'), tls()],
    'sys_container_get_qquota': [kpage('ucon'), tls()],
    'sys_container_move_quota': [kpage('from'), kpage('to')],
    'sys_container_move_uquota': [kpage('from'), kpage('to')],
    'sys_container_get_parent': [kpage('ucon'), tls()],
    'sys_reserve_page': [kpage('ucon'), slot()],
    'sys_alloc_tag': [slot(), tls()],
    'do_alloc_container': [kpage('ucon'), i64('slot'), i64('sslot'),
                           i64('islot'), label('secrecy', check=True), label('integrity')],
    'do_alloc_block': [kpage('ucon'), i64('slot'), i64('sslot'),
                       i64('islot'), label('secrecy'), label('integrity')],
    'do_alloc_thread': [kpage('ucon'), i64('slot'), i64('sslot'), i64('islot'),
                        i64('oslot'), label('secrecy', check=True), label('integrity'),
                        label('requested_ownership'), i64('tslot'),
                        kpage('ugatep', concat=True), kpage('ugate_parentp', concat=True)],
    'do_alloc_gate': [kpage('ucon'), i64('slot'), i64('sslot'), i64('islot'),
                      i64('oslot'), i64('gslot'), label('secrecy', check=True), label('integrity'),
                      label('ownership'), label('guard', check=True), kpage('upud', concat=True),
                      kpage('upud_parent', concat=True), i64('entry'), i64('gatearg0'),
                      i64('gatearg1'), i64('gatearg2')],
    'do_alloc_directory_pud': [kpage('ucon'), i64('slot'), i64('sslot'), i64('islot'), label('secrecy', check=True), label('integrity')],
    'do_alloc_directory_pmd': [kpage('ucon'), i64('slot'), i64('sslot'), i64('islot'), label('secrecy', check=True), label('integrity')],
    'sys_directory_get_slot': [kpage('usym'), slot(), tls()],
    'sys_directory_link_pmd': [kpage('upud'), slot(), kpage('ucon'), slot()],
    'do_directory_link_block': [kpage('upmd'), slot(), kpage('ucon'), slot(), i64('pteval')],
    'sys_directory_unlink_pmd': [kpage('upud'), slot()],
    'sys_directory_unlink_block': [kpage('upmd'), slot()],

    'sys_free_gate': [kpage('ucon'), i64('slot')],
    'sys_free_block': [kpage('ucon'), i64('slot')],
    'sys_free_directory_pud': [kpage('ucon'), i64('slot')],
    'sys_free_directory_pmd': [kpage('ucon'), i64('slot')],
    'sys_free_thread': [kpage('ucon'), i64('slot')],

    'sys_page_get_type': [kpage('ucon'), slot(), tls()],
    'sys_page_get_label': [kpage('ucon'), slot(), tls(), tls()],
    'sys_page_get_name': [kpage('ucon'), slot(), tls()],
    'sys_page_set_name': [kpage('ucon'), slot(), tls()],
    'sys_page_get_metadata': [kpage('ucon'), slot(), tls()],
    'sys_page_set_metadata': [kpage('ucon'), slot(), tls()],
    'do_gate_enter': [kpage('ucon'), slot(), label('requested_ownership'), i64('arg')],
    'sys_gate_get_label': [kpage('ucon'), slot(), tls(), tls(), tls()],
    'sys_thread_get_state': [kpage('ucon'), slot(), tls()],
    'sys_self_get_pud': [tls()],
    'sys_self_get_label': [i64('sto',), i64('ito'), i64('oto')],
    'do_self_set_label': [label('requested_secrecy'),
                          label('requested_integrity'),
                          label('requested_ownership')],

    'sys_self_get': [tls()],

    'sys_alloc_quantum': [kpage('ucon'), i64('qid'), kpage('uthread')],
    'sys_container_move_qquota': [kpage('from'), i64('qid'), kpage('to')],

    'sched_next': [],
}

proto = p.Prototype(full_prototypes)
