import sys
import z3

import libirpy.util as util

import datatypes as dt
import invariants


def ok(state):
    return invariants.spec_invariants(state)


def freelist_ok(state):
    conj = []

    cid = util.FreshBitVec('cid', dt.page_id_t)
    id = util.FreshBitVec('id', dt.page_id_t)
    idx = util.FreshBitVec('idx', dt.size_t)

    # quota never exceeds NR_PAGES
    conj.append(z3.ForAll([cid], z3.Implies(
        dt.page_is_valid(cid),
        z3.ULE(state.pages[cid].quota, dt.NR_PAGES))))

    # `next` field on a container is the head of the list
    conj.append(z3.ForAll([cid], z3.Implies(
        z3.And(
            dt.page_is_valid(cid),
            state.pages[cid].type == dt.PAGE_TYPE_CONTAINER,
            state.pages[cid].quota != 0),
        state.pages[cid].list(0) == state.pages[cid].next)))

    # if the list is empty, next is PAGE_ID_INVALID
    conj.append(z3.ForAll([cid], util.Implies(
        z3.And(
            dt.page_is_valid(cid),
            state.pages[cid].type == dt.PAGE_TYPE_CONTAINER,
            state.pages[cid].quota == 0),
        state.pages[cid].next == dt.PAGE_ID_INVALID)))

    # valid index in the list produces a valid page
    conj.append(z3.ForAll([cid, idx], z3.Implies(
        z3.And(
            dt.page_is_valid(cid),
            z3.ULT(idx, dt.NR_PAGES)),
        dt.page_is_valid(state.pages[cid].list(idx)))))

    # valid page produces a valid index in the list inverse
    conj.append(z3.ForAll([cid, id], z3.Implies(
        z3.And(
            dt.page_is_valid(cid),
            dt.page_is_valid(id)),
        z3.ULT(state.pages[cid].list_inv(id), dt.NR_PAGES))))

    # list is bijective
    conj.append(z3.ForAll([cid, id, idx], z3.Implies(
        z3.And(
            dt.page_is_valid(cid),
            dt.page_is_valid(id),
            z3.ULT(idx, dt.NR_PAGES)),
        z3.And(
            state.pages[cid].list(state.pages[cid].list_inv(id)) == id,
            state.pages[cid].list_inv(state.pages[cid].list(idx)) == idx))))

    # everything "below" size of list, is unallocated and has `cid` as parent.
    conj.append(z3.ForAll([cid, id], z3.Implies(
        z3.And(
            dt.page_is_valid(cid),
            dt.page_is_valid(id)),
        z3.And(
            z3.Implies(
                z3.And(
                    state.pages[id].type == dt.PAGE_TYPE_NONE,
                    state.pages[id].parent == cid),
                z3.ULT(state.pages[cid].list_inv(id), state.pages[cid].quota)),
            z3.Implies(
                z3.Not(z3.And(
                    state.pages[id].type == dt.PAGE_TYPE_NONE,
                    state.pages[id].parent == cid)),
                z3.UGE(state.pages[cid].list_inv(id), state.pages[cid].quota))))))

    conj.append(z3.ForAll([cid, idx], z3.Implies(
        z3.And(
            dt.page_is_valid(cid),
            z3.ULT(idx, state.pages[cid].quota)),
        state.pages[state.pages[cid].list(idx)].next == util.If(idx ==
            state.pages[cid].quota - 1, dt.PAGE_ID_INVALID,
            state.pages[cid].list(idx+1)))))

    return z3.And(*conj)

def freelist1_ok(state):
    conj = []

    cid = util.FreshBitVec('cid', dt.page_id_t)
    id = util.FreshBitVec('id', dt.page_id_t)
    idx = util.FreshBitVec('idx', dt.size_t)

    # quota never exceeds NR_PAGES
    conj.append(z3.ForAll([cid], z3.Implies(
        dt.page_is_valid(cid),
        z3.ULE(state.pages[cid].quota, dt.NR_PAGES))))

    # `next` field on a container is the head of the list
    conj.append(z3.ForAll([cid], z3.Implies(
        z3.And(
            dt.page_is_valid(cid),
            state.pages[cid].type == dt.PAGE_TYPE_CONTAINER,
            state.pages[cid].quota != 0),
        state.pages[cid].list(0) == state.pages[cid].next)))

    # if the list is empty, next is PAGE_ID_INVALID
    conj.append(z3.ForAll([cid], util.Implies(
        z3.And(
            dt.page_is_valid(cid),
            state.pages[cid].type == dt.PAGE_TYPE_CONTAINER,
            state.pages[cid].quota == 0),
        state.pages[cid].next == dt.PAGE_ID_INVALID)))

    # valid index in the list produces a valid page
    conj.append(z3.ForAll([cid, idx], z3.Implies(
        z3.And(
            dt.page_is_valid(cid),
            z3.ULT(idx, dt.NR_PAGES)),
        dt.page_is_valid(state.pages[cid].list(idx)))))

    # valid page produces a valid index in the list inverse
    conj.append(z3.ForAll([cid, id], z3.Implies(
        z3.And(
            dt.page_is_valid(cid),
            dt.page_is_valid(id)),
        z3.ULT(state.pages[cid].list_inv(id), dt.NR_PAGES))))

    # list is bijective
    conj.append(z3.ForAll([cid, id, idx], z3.Implies(
        z3.And(
            dt.page_is_valid(cid),
            dt.page_is_valid(id),
            z3.ULT(idx, dt.NR_PAGES)),
        z3.And(
            state.pages[cid].list(state.pages[cid].list_inv(id)) == id,
            state.pages[cid].list_inv(state.pages[cid].list(idx)) == idx))))

    # everything "below" size of list, is unallocated and has `cid` as parent.
    conj.append(z3.ForAll([cid, id], z3.Implies(
        z3.And(
            dt.page_is_valid(cid),
            dt.page_is_valid(id)),
        z3.And(
            z3.Implies(
                z3.And(
                    state.pages[id].type == dt.PAGE_TYPE_NONE,
                    state.pages[id].parent == cid),
                z3.ULT(state.pages[cid].list_inv(id), state.pages[cid].quota)),
            z3.Implies(
                z3.Not(z3.And(
                    state.pages[id].type == dt.PAGE_TYPE_NONE,
                    state.pages[id].parent == cid)),
                z3.UGE(state.pages[cid].list_inv(id), state.pages[cid].quota))))))

    return z3.And(*conj)


def freelist2_ok(state):
    conj = []

    cid = util.FreshBitVec('cid', dt.page_id_t)
    idx = util.FreshBitVec('idx', dt.size_t)

    conj.append(z3.ForAll([cid, idx], z3.Implies(
        z3.And(
            dt.page_is_valid(cid),
            z3.ULT(idx, state.pages[cid].quota)),
        state.pages[state.pages[cid].list(idx)].next == util.If(idx ==
            state.pages[cid].quota - 1, dt.PAGE_ID_INVALID,
            state.pages[cid].list(idx+1)))))

    return z3.And(*conj)


def ufreelist_ok(state):
    conj = []

    cid = util.FreshBitVec('cid', dt.page_id_t)
    id = util.FreshBitVec('id', dt.upage_id_t)
    bid = util.FreshBitVec('bid', dt.page_id_t)
    idx = util.FreshBitVec('idx', dt.size_t)

    # every free upage's parent is a valid container
    conj.append(z3.ForAll([id], z3.Implies(
        z3.And(
            dt.page2m_is_valid(id),
            state.upages[id].available,
        ),
        z3.And(
            dt.page_is_valid(state.upages[id].parent),
            state.pages[state.upages[id].parent].type == dt.PAGE_TYPE_CONTAINER))))

    # every upage's parent is a valid block
    conj.append(z3.ForAll([id], z3.Implies(
        z3.And(
            dt.page2m_is_valid(id),
            z3.Not(state.upages[id].available),
        ),
        z3.And(
            dt.page_is_valid(state.upages[id].parent),
            state.pages[state.upages[id].parent].type == dt.PAGE_TYPE_BLOCK,
            state.pages[state.upages[id].parent].data(0) == id))))

    # every block's upage is not marked as free
    conj.append(z3.ForAll([bid], z3.Implies(
        z3.And(
            dt.page_is_valid(bid),
            state.pages[bid].type == dt.PAGE_TYPE_BLOCK,
        ),
        z3.And(
            dt.page2m_is_valid(state.pages[bid].data(0)),
            z3.Not(state.upages[state.pages[bid].data(0)].available),
            state.upages[state.pages[bid].data(0)].parent == bid))))

    #########

    # uquota never exceeds NR_PAGES2M
    conj.append(z3.ForAll([cid], z3.Implies(
        dt.page_is_valid(cid),
        z3.ULE(state.pages[cid].uquota, dt.NR_PAGES2M))))

    # `unext` field on a container is the head of the list
    conj.append(z3.ForAll([cid], z3.Implies(
        z3.And(
            dt.page_is_valid(cid),
            state.pages[cid].type == dt.PAGE_TYPE_CONTAINER,
            state.pages[cid].uquota != 0),
        state.pages[cid].ulist(0) == state.pages[cid].unext)))

    # if the list is empty, next is PAGE2M_ID_INVALID
    conj.append(z3.ForAll([cid], util.Implies(
        z3.And(
            dt.page_is_valid(cid),
            state.pages[cid].type == dt.PAGE_TYPE_CONTAINER,
            state.pages[cid].uquota == 0),
        state.pages[cid].unext == dt.PAGE2M_ID_INVALID)))

    # valid index in the list produces a valid page
    conj.append(z3.ForAll([cid, idx], z3.Implies(
        z3.And(
            dt.page_is_valid(cid),
            z3.ULT(idx, dt.NR_PAGES2M)),
        dt.page2m_is_valid(state.pages[cid].ulist(idx)))))

    # valid page produces a valid index in the list inverse
    conj.append(z3.ForAll([cid, id], z3.Implies(
        z3.And(
            dt.page_is_valid(cid),
            dt.page2m_is_valid(id)),
        z3.ULT(state.pages[cid].ulist_inv(id), dt.NR_PAGES2M))))

    # list is bijective
    conj.append(z3.ForAll([cid, id, idx], z3.Implies(
        z3.And(
            dt.page_is_valid(cid),
            dt.page2m_is_valid(id),
            z3.ULT(idx, dt.NR_PAGES2M)),
        z3.And(
            state.pages[cid].ulist(state.pages[cid].ulist_inv(id)) == id,
            state.pages[cid].ulist_inv(state.pages[cid].ulist(idx)) == idx))))

    # everything "below" size of list, is unallocated and has `cid` as parent.
    conj.append(z3.ForAll([cid, id], z3.Implies(
        z3.And(
            dt.page_is_valid(cid),
            dt.page2m_is_valid(id)),
        z3.And(
            z3.Implies(
                z3.And(
                    state.upages[id].available,
                    state.upages[id].parent == cid),
                z3.ULT(state.pages[cid].ulist_inv(id), state.pages[cid].uquota)),
            z3.Implies(
                z3.Not(z3.And(
                    state.upages[id].available,
                    state.upages[id].parent == cid)),
                z3.UGE(state.pages[cid].ulist_inv(id), state.pages[cid].uquota))))))

    conj.append(z3.ForAll([cid, idx], z3.Implies(
        z3.And(
            dt.page_is_valid(cid),
            z3.ULT(idx, state.pages[cid].uquota)),
        state.upages[state.pages[cid].ulist(idx)].next == util.If(idx ==
            state.pages[cid].uquota - 1, dt.PAGE2M_ID_INVALID,
            state.pages[cid].ulist(idx+1)))))

    return z3.And(*conj)


def label_unique_ok(state):
    conj = []

    id = util.FreshBitVec('id', dt.page_id_t)
    conj.append(z3.ForAll([id], z3.Implies(
        z3.And(
            dt.page_is_valid(id),
            z3.UGT(state.pages[id].type, dt.PAGE_TYPE_LABEL)),
        z3.And(
            state.pages[state.pages[id].secrecy].label_type == dt.LABEL_TYPE_SECRECY,
            state.pages[state.pages[id].secrecy].label_owner == id,

            state.pages[state.pages[id].integrity].label_type == dt.LABEL_TYPE_INTEGRITY,
            state.pages[state.pages[id].integrity].label_owner == id,

            z3.Implies(state.pages[id].type == dt.PAGE_TYPE_THREAD, z3.And(
                       state.pages[state.pages.ownership(id)].label_owner == id,
                       state.pages[state.pages.ownership(id)].label_type == dt.LABEL_TYPE_THREAD_OWNERSHIP)),

            z3.Implies(state.pages[id].type == dt.PAGE_TYPE_GATE, z3.And(
                       state.pages[state.pages.ownership(id)].label_owner == id,
                       state.pages[state.pages.ownership(id)].label_type == dt.LABEL_TYPE_GATE_OWNERSHIP)),

            z3.Implies(state.pages[id].type == dt.PAGE_TYPE_GATE, z3.And(
                       state.pages[state.pages.gate_guard(id)].label_owner == id,
                       state.pages[state.pages.gate_guard(id)].label_type == dt.LABEL_TYPE_GATE_GUARD)),
        ))))

    return z3.And(*conj)


def tls_unique_ok(state):
    conj = []

    id = util.FreshBitVec('id', dt.page_id_t)
    conj.append(z3.ForAll([id], z3.Implies(
        z3.And(
            dt.page_is_valid(id),
            state.pages[id].type == dt.PAGE_TYPE_THREAD),
        z3.And(
            dt.page_is_valid(state.pages[id].data(1)),
            state.pages[state.pages[id].data(1)].type == dt.PAGE_TYPE_BLOCK,
            state.pages[state.pages[id].data(1)].is_tls,
            state.pages[state.pages[id].data(1)].tls_owner == id))))

    return z3.And(*conj)


def tags_unused_ok(state):
    conj = []

    la = util.FreshBitVec('la', dt.page_id_t)
    id = util.FreshBitVec('id', dt.page_id_t)
    ctr = util.FreshBitVec('ctr', dt.size_t)

    conj.append(z3.ForAll([la, id, ctr], z3.Implies(
        z3.And(
            dt.page_is_valid(la),
            dt.page_is_valid(id),
            state.pages[la].type == dt.PAGE_TYPE_LABEL,
            z3.Or(
                state.pages[la].label_type == dt.LABEL_TYPE_INTEGRITY,
                state.pages[la].label_type == dt.LABEL_TYPE_THREAD_OWNERSHIP,
                state.pages[la].label_type == dt.LABEL_TYPE_GATE_OWNERSHIP),
            z3.ULE(state.pages[id].tag_counter, ctr)),
        z3.Not(state.pages.label[la].label(z3.Concat(ctr, id))))))

    return z3.And(*conj)


def parent_link_consistent_ok(state):
    conj = []

    id = util.FreshBitVec('id', dt.page_id_t)
    slot = util.FreshBitVec('slot', dt.size_t)

    # Every page's parent is a container
    conj.append(z3.ForAll([id], z3.Implies(
        z3.And(
            dt.page_is_valid(id),
            dt.page_type_normal(state.pages[id].type)),
        z3.And(
            dt.page_is_valid(state.pages[id].parent),
            z3.ULT(state.pages[id].parent_slot, dt.CONTAINER_NR_PAGES),
            state.pages[state.pages[id].parent].type == dt.PAGE_TYPE_CONTAINER))))

    conj.append(z3.ForAll([id, slot], z3.Implies(
        z3.And(
            dt.page_is_valid(id),
            z3.ULT(slot, dt.CONTAINER_NR_PAGES),
            state.pages[id].type == dt.PAGE_TYPE_CONTAINER,
            dt.page_is_valid(state.pages[id].data(slot))),
        z3.And(
            dt.page_type_normal(state.pages[state.pages[id].data(slot)].type),
            # tls blocks never appear in a container
            z3.Not(state.pages[state.pages[id].data(slot)].is_tls),
            state.pages[state.pages[id].data(slot)].parent == id,
            state.pages[state.pages[id].data(slot)].parent_slot == slot))))

    return z3.And(*conj)


def current_thread_valid(state):
    return state.pages[state.current].data(2) != dt.THREAD_STATE_HALTED


def spec_to_lemma(name):
    """Return a list of lemmas that spec `name` depends on."""
    if name.endswith('64'):
        name = name[:-2]

    if name == 'sys_self_get_pud':
        lemmas = ['ok']
    elif name == 'sys_container_move_uquota':
        lemmas = ['ok', 'ufreelist_ok']
    elif name == 'sys_container_move_quota':
        lemmas = ['ok', 'freelist_ok']
    elif name == 'do_self_set_label':
        lemmas = ['ok', 'current_thread_valid', 'label_unique_ok', 'tls_unique_ok']
    elif name in ['sys_page_get_label', 'sys_gate_get_label', 'sys_self_get_label']:
        lemmas = ['ok', 'current_thread_valid', 'label_unique_ok', 'tls_unique_ok']
    elif name == 'sys_container_get_parent':
        lemmas = ['ok']
    elif name == 'sys_reserve_page':
        lemmas = ['ok', 'freelist_ok']
    elif name == 'do_alloc_block':
        lemmas = ['ok', 'tls_unique_ok', 'current_thread_valid', 'ufreelist_ok']
    elif name.startswith('do_alloc'):
        lemmas = ['ok', 'tls_unique_ok', 'current_thread_valid']
    elif name == 'sys_container_get_slot':
        lemmas = ['ok']
    elif name == 'sys_page_set_metadata':
        lemmas = ['ok', 'label_unique_ok', 'tls_unique_ok']
    elif name in ['sys_directory_link_pmd', 'do_directory_link_block', 'sys_directory_get_slot']:
        lemmas = ['ok']
    elif name == 'sys_page_set_name':
        lemmas = ['ok', 'label_unique_ok', 'tls_unique_ok']
    elif name == 'sys_free_thread':
        lemmas = ['ok', 'label_unique_ok', 'tls_unique_ok',
        'current_thread_valid', 'freelist_ok']
    elif name.startswith('sys_alloc_tag'):
        # Tag allocation changes tag_counter, which is observable through
        # the per-container freelist to any thread that can read the
        # freelist. We need to pull in freelist lemma here to establish that
        # an allocated thread can not be in any freelist to prove NI for tag_alloc.
        lemmas = ['ok', 'label_unique_ok', 'freelist_ok']
    elif name.startswith('do_gate_enter'):
        lemmas = ['ok', 'label_unique_ok']
    else:
        lemmas = ['ok', 'current_thread_valid', 'freelist_ok',
                  'ufreelist_ok', 'label_unique_ok', 'tls_unique_ok']

    cur = sys.modules[__name__]
    return [getattr(cur, i) for i in lemmas]
