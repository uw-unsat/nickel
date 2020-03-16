# -*- encoding: utf8
import z3

import libirpy.util as util
import datatypes as dt
import label as l
import errno


def alloc_label(state, label_pn, label, owner, type):
    state.pages[label_pn].type = dt.i64(dt.PAGE_TYPE_LABEL)
    state.pages[label_pn].secrecy = dt.PAGE_ID_INVALID
    state.pages[label_pn].integrity = dt.PAGE_ID_INVALID
    state.pages.label.label = lambda pn, tag, oldfn: util.If(pn == label_pn, label.has(tag), oldfn(pn, tag))
    state.pages.data = lambda pn, idx, oldfn: util.If(pn == label_pn, label.data(idx), oldfn(pn, idx))
    state.pages[label_pn].label_owner = owner
    state.pages[label_pn].label_type = type
    return state


def set_label(state, label_pn, l):
    state.pages.label.label = lambda pn, tag, oldfn: \
            util.If(pn == label_pn, l.has(tag), oldfn(pn, tag))

    state.pages.data = lambda pn, idx, oldfn: \
            util.If(pn == label_pn, l.data(idx), oldfn(pn, idx))


def sys_container_get_root(old, to):
    new = old.copy()

    cond = z3.ULE(to, dt.TLS_NR_SLOTS - 2)

    new.tls[to] = old.root_container_id
    new.tls[to+1] = old.pages[old.root_container_id].generation

    return cond, util.If(cond, new, old)


def sys_container_get_root64(old, to):
    new = old.copy()

    cond = util.Cases(
        (z3.Not(z3.ULE(to, dt.TLS_NR_SLOTS - 1)), -errno.EINVAL),
        default=util.i64(0))

    new.tls[to] = old.root_container_id

    return cond, util.If(cond.cond(negate=True), new, old)


def sys_container_get_slot(old, container, slot, to):
    new = old.copy()

    cond = z3.And(
        old.pages.is_type(container, dt.PAGE_TYPE_CONTAINER),
        z3.ULT(slot, dt.CONTAINER_NR_PAGES),
        z3.ULE(to, dt.TLS_NR_SLOTS - 2),
        old.pages.can_read(old.current, container),
        dt.page_is_valid(old.pages[container[0]].data(slot)),
    )

    id = old.pages[container[0]].data(slot)

    new.tls[to+0] = id
    new.tls[to+1] = old.pages[id].generation

    return cond, util.If(cond, new, old)


def sys_container_get_slot64(old, container, slot, to):
    new = old.copy()

    cond = util.Cases(
        (z3.UGE(slot, dt.CONTAINER_NR_PAGES), -errno.EINVAL),
        (z3.Not(old.pages.is_type(container, dt.PAGE_TYPE_CONTAINER)),
            -errno.EACCES),
        (z3.Not(old.pages.can_read(old.current, container)),
            -errno.EACCES),
        (z3.Not(dt.page_is_valid(old.pages[container].data(slot))),
            -errno.EINVAL),
        (z3.Not(z3.ULE(to, dt.TLS_NR_SLOTS - 1)),
            -errno.EINVAL),
        default=util.i64(0))

    id = old.pages[container].data(slot)
    new.tls[to] = id

    return cond, util.If(cond.cond(negate=True), new, old)


def sys_container_get_quota(old, container, to):
    cond = z3.And(
        old.pages.is_type(container, dt.PAGE_TYPE_CONTAINER),
        z3.ULE(to, dt.TLS_NR_SLOTS - 1),
        old.pages.can_read(old.current, container),
    )

    new = old.copy()

    new.tls[to] = old.pages[container[0]].quota

    return cond, util.If(cond, new, old)


def sys_container_get_uquota(old, container, to):
    new = old.copy()

    cond = z3.And(
        old.pages.is_type(container, dt.PAGE_TYPE_CONTAINER),
        z3.ULE(to, dt.TLS_NR_SLOTS - 1),
        old.pages.can_read(old.current, container),
    )

    new.tls[to] = old.pages[container[0]].uquota

    return cond, util.If(cond, new, old)


def sys_container_move_quota(old, frm, to):
    cond = z3.And(
        # both arguments are containers
        old.pages.is_type(frm, dt.PAGE_TYPE_CONTAINER),
        old.pages.is_type(to, dt.PAGE_TYPE_CONTAINER),

        # current thread can read/write both containers
        old.pages.can_read_write(old.current, frm),
        old.pages.can_read_write(old.current, to),

        # container has enough quota to give away
        old.pages[frm[0]].quota != 0,
    )

    new = old.copy()

    popped = new.pages.freelist_pop(frm[0])
    new.pages.freelist_push(to[0], popped)

    return cond, util.If(cond, new, old)


def sys_container_move_uquota(old, frm, to):
    cond = z3.And(
        # both arguments are containers
        old.pages.is_type(frm, dt.PAGE_TYPE_CONTAINER),
        old.pages.is_type(to, dt.PAGE_TYPE_CONTAINER),

        # current thread can read/write both containers
        old.pages.can_read_write(old.current, frm),
        old.pages.can_read_write(old.current, to),

        # container has enough quota to give away
        old.pages[frm[0]].uquota != 0,
    )

    new = old.copy()

    unext = new.pages[frm[0]].unext
    new.pages[frm[0]].unext = new.upages[unext].next
    new.pages[frm[0]].uquota -= 1

    new.pages.ulist = lambda cid, idx, oldfn: \
            util.If(z3.And(cid == frm[0], idx == dt.NR_PAGES2M),
                    unext,
                    oldfn(cid, idx))

    new.pages.ulist_inv = lambda cid, pn, oldfn: \
            util.If(z3.And(cid == frm[0], pn == unext),
                    dt.i64(dt.NR_PAGES2M),
                    oldfn(cid, pn))

    new.pages.ulist = lambda cid, idx, oldfn: \
            util.If(cid == frm[0],
                    oldfn(cid, idx+1),
                    oldfn(cid, idx))

    new.pages.ulist_inv = lambda cid, pn, oldfn: \
            util.If(cid == frm[0],
                    oldfn(cid, pn)-1,
                    oldfn(cid, pn))

    new.pages[to[0]].uquota += 1

    pos = new.pages[to[0]].ulist_inv(unext)
    last = new.pages[to[0]].ulist(dt.NR_PAGES2M-1)

    new.pages.ulist = lambda cid, idx, oldfn: \
            util.If(z3.And(cid == to[0], idx == 0),
                    unext,
                    util.If(cid == to[0],
                        util.If(z3.And(cid == to[0], idx-1 == pos),
                                last,
                                oldfn(cid, idx-1)),
                        oldfn(cid, idx)))

    new.pages.ulist_inv = lambda cid, pn, oldfn: \
            util.If(z3.And(cid == to[0], pn == unext),
                    dt.i64(0),
                    util.If(cid == to[0],
                        util.If(z3.And(cid == to[0], pn == last),
                                pos,
                                oldfn(cid, pn))+1,
                        oldfn(cid, pn)))

    new.upages[unext].parent = to[0]
    new.upages[unext].next = new.pages[to[0]].unext
    new.pages[to[0]].unext = unext

    return cond, util.If(cond, new, old)


def sys_container_move_qquota(old, frm, qid, to):
    cond = util.Cases(
        (z3.Not(dt.quantum_is_valid(qid)),
            -errno.EINVAL),

        # can read and write both containers
        (z3.Not(old.pages.is_type(frm, dt.PAGE_TYPE_CONTAINER)),
            -errno.EACCES),
        (z3.Not(old.pages.can_read_write(old.current, frm)),
            -errno.EACCES),

        # Sufficient quota
        (old.pages[frm[0]].qquota == 0,
            -errno.EDQUOT),

        (old.time[qid].container != frm[0],
            -errno.ENOENT),

        (z3.Not(old.pages.is_type(to, dt.PAGE_TYPE_CONTAINER)),
            -errno.EACCES),
        (z3.Not(old.pages.can_read_write(old.current, to)),
            -errno.EACCES),


        default=util.i64(0))

    new = old.copy()

    new.pages[frm[0]].qquota -= 1
    new.pages[to[0]].qquota += 1
    new.time[qid].container = to[0]

    return cond, util.If(cond.cond(negate=True), new, old)


def sys_container_get_qquota(old, container, to):
    cond = util.Cases(
        (z3.Not(old.pages.is_type(container, dt.PAGE_TYPE_CONTAINER)),
            -errno.EACCES),
        (z3.Not(old.pages.can_read(old.current, container)),
            -errno.EACCES),
        (z3.UGT(to, dt.TLS_NR_SLOTS - 1),
            -errno.EINVAL),
        default=util.i64(0))

    new = old.copy()
    new.tls[to] = old.pages[container[0]].qquota

    return cond, util.If(cond.cond(negate=True), new, old)


def sys_container_get_parent(old, container, to):
    cond = z3.And(
        old.pages.is_type(container, dt.PAGE_TYPE_CONTAINER),
        z3.ULE(to, dt.TLS_NR_SLOTS - 2),
        old.pages.can_read(old.current, container),
    )

    new = old.copy()

    new.tls[to] = old.pages[container[0]].parent
    new.tls[to+1] = old.pages[new.tls(to)].generation

    return cond, util.If(cond, new, old)


def sys_reserve_page(old, container, slot):
    cond = z3.And(
        z3.ULT(slot, dt.CONTAINER_NR_PAGES),
        old.pages.is_type(container, dt.PAGE_TYPE_CONTAINER),
        old.pages.can_read_write(old.current, container),
        old.pages[container[0]].quota != 0,
        z3.Not(dt.page_is_valid(old.pages[container[0]].data(slot))),
    )

    new = old.copy()

    # pop from the freelist
    page = new.pages.freelist_pop(container[0])

    new.pages[page].is_tls = False
    new.pages[page].generation += 1
    new.pages[page].type = dt.PAGE_TYPE_UNTYPED
    new.pages[page].name = dt.i64(0)
    new.pages[page].metadata = dt.i64(0)
    new.pages[page].data = dt.i64(0)
    new.pages[page].secrecy = dt.PAGE_ID_INVALID
    new.pages[page].integrity = dt.PAGE_ID_INVALID
    new.pages[page].quota = 0
    new.pages[page].next = dt.PAGE_ID_INVALID

    new.pages[page].parent = container[0]
    new.pages[page].parent_slot = slot

    new.pages[container[0]].data[slot] = page

    return cond, util.If(cond, new, old)


def sys_alloc_quantum(old, container, qid, thread):
    cond = util.Cases(
            (z3.Not(dt.page_is_valid(thread[0])),
                -errno.EINVAL),
            (z3.Not(dt.quantum_is_valid(qid)),
                -errno.EINVAL),
            (z3.Not(old.pages.is_type(container, dt.PAGE_TYPE_CONTAINER)),
                -errno.EACCES),
            (z3.Not(old.pages.can_read_write(old.current, container)),
                -errno.EACCES),
            (old.pages[container[0]].qquota == 0,
                -errno.EDQUOT),
            (old.time[qid].container != container[0],
                -errno.ENOENT),
            default=util.i64(0))
    new = old.copy()

    new.time[qid].thread = thread[0]

    return cond, util.If(cond.cond(negate=True), new, old)


def sys_alloc_tag(old, slot, to):
    ownership = old.pages.ownership(old.current)

    cond = z3.And(
        z3.ULT(slot, dt.LABEL_NR_TAGS),
        z3.ULT(old.pages[old.current].tag_counter, dt.MAX_INT64),
        z3.Concat(old.pages[ownership].data(slot*2+1),
                  old.pages[ownership].data(slot*2)) == dt.MAX_INT128,
        z3.ULE(to, dt.TLS_NR_SLOTS - 2),
    )

    new = old.copy()

    tag_lo = old.current
    tag_hi = old.pages[old.current].tag_counter
    tag = z3.Concat(tag_hi, tag_lo)

    new.pages[old.current].tag_counter += 1
    new.pages.label[ownership].label[tag] = True
    new.pages[ownership].data[slot*2]     = tag_lo
    new.pages[ownership].data[slot*2+1]   = tag_hi

    new.tls[to+0] = tag_lo
    new.tls[to+1] = tag_hi

    return cond, util.If(cond, new, old)


def alloc_page(old, ucon, slot, sslot, islot, requested_secrecy, requested_integrity, type):
    thread_secrecy = old.pages.secrecy_label(old.current)
    thread_integrity = old.pages.integrity_label(old.current)
    thread_ownership = old.pages.ownership_label(old.current)

    page = old.pages[ucon[0]].data(slot)
    secrecy_label = old.pages[ucon[0]].data(sslot)
    integrity_label = old.pages[ucon[0]].data(islot)

    cond = z3.And(
        old.pages.is_type(ucon, dt.PAGE_TYPE_CONTAINER),

        z3.ULT(slot, dt.CONTAINER_NR_PAGES),
        z3.ULT(sslot, dt.CONTAINER_NR_PAGES),
        z3.ULT(islot, dt.CONTAINER_NR_PAGES),

        z3.Distinct(slot, sslot, islot),
        z3.Distinct(old.pages[ucon[0]].data(sslot), old.pages[ucon[0]].data(islot)),

        old.pages.can_read_write(old.current, ucon),

        old.pages.is_type(page, dt.PAGE_TYPE_UNTYPED),
        old.pages.is_type(secrecy_label, dt.PAGE_TYPE_UNTYPED),
        old.pages.is_type(integrity_label, dt.PAGE_TYPE_UNTYPED),

        # T ⊑⁺ O
        l.is_subsetx(thread_secrecy, requested_secrecy.has, thread_ownership),
        l.is_subsetx(requested_integrity.has, thread_integrity, thread_ownership),
    )

    new = old.copy()

    # Allocate secrecy / integrity label pages.
    new = alloc_label(new, secrecy_label, requested_secrecy, page, dt.LABEL_TYPE_SECRECY)
    new = alloc_label(new, integrity_label, requested_integrity, page, dt.LABEL_TYPE_INTEGRITY)

    new.pages[page].type = type

    # Not needed. Should already be set (invariants)
    new.pages[page].parent = ucon[0]
    new.pages[page].parent_slot = slot

    if type == dt.PAGE_TYPE_CONTAINER:
        new.pages[page].quota = dt.i64(0)
        new.pages[page].uquota = dt.i64(0)
        new.pages[page].qquota = dt.i64(0)
        new.pages[page].next = dt.PAGE_ID_INVALID
        new.pages[page].unext = dt.PAGE2M_ID_INVALID
        new.pages[page].data = dt.MAX_INT64
    elif type == dt.PAGE_TYPE_PUD or type == dt.PAGE_TYPE_PMD:
        new.pages[page].data = dt.i64(0)

    new.pages[page].secrecy = secrecy_label
    new.pages[page].integrity = integrity_label

    new.pages[ucon[0]].data[sslot] = dt.PAGE_ID_INVALID
    new.pages[ucon[0]].data[islot] = dt.PAGE_ID_INVALID

    return cond, util.If(cond, new, old)


def do_alloc_container(old, ucon, slot, sslot, islot, requested_secrecy, requested_integrity):
    return alloc_page(old, ucon, slot, sslot, islot, requested_secrecy, requested_integrity, dt.PAGE_TYPE_CONTAINER)


def do_alloc_block(old, ucon, slot, sslot, islot, requested_secrecy, requested_integrity):
    thread_secrecy = old.pages.secrecy_label(old.current)
    thread_integrity = old.pages.integrity_label(old.current)
    thread_ownership = old.pages.ownership_label(old.current)

    block = old.pages[ucon[0]].data(slot)
    secrecy_label = old.pages[ucon[0]].data(sslot)
    integrity_label = old.pages[ucon[0]].data(islot)

    cond = z3.And(
        old.pages.is_type(ucon, dt.PAGE_TYPE_CONTAINER),

        z3.ULT(slot, dt.CONTAINER_NR_PAGES),
        z3.ULT(sslot, dt.CONTAINER_NR_PAGES),
        z3.ULT(islot, dt.CONTAINER_NR_PAGES),

        old.pages[ucon[0]].uquota != 0,

        z3.Distinct(slot, sslot, islot),
        z3.Distinct(old.pages[ucon[0]].data(sslot), old.pages[ucon[0]].data(islot)),

        old.pages.can_read_write(old.current, ucon),

        old.pages.is_type(block, dt.PAGE_TYPE_UNTYPED),
        old.pages.is_type(secrecy_label, dt.PAGE_TYPE_UNTYPED),
        old.pages.is_type(integrity_label, dt.PAGE_TYPE_UNTYPED),

        # T ⊑⁺ O
        l.is_subsetx(thread_secrecy, requested_secrecy.has, thread_ownership),
        l.is_subsetx(requested_integrity.has, thread_integrity, thread_ownership),

    )

    new = old.copy()

    # Allocate secrecy / integrity label pages.
    new = alloc_label(new, secrecy_label, requested_secrecy, block, dt.LABEL_TYPE_SECRECY)
    new = alloc_label(new, integrity_label, requested_integrity, block, dt.LABEL_TYPE_INTEGRITY)

    # pop upage
    uid = new.pages[ucon[0]].unext
    new.pages[ucon[0]].unext = new.upages[uid].next
    new.pages[ucon[0]].uquota -= 1

    new.pages.ulist = lambda cid, idx, oldfn: \
            util.If(z3.And(cid == ucon[0], idx == dt.NR_PAGES2M),
                    uid,
                    oldfn(cid, idx))

    new.pages.ulist_inv = lambda cid, pn, oldfn: \
            util.If(z3.And(cid == ucon[0], pn == uid),
                    dt.i64(dt.NR_PAGES2M),
                    oldfn(cid, pn))

    new.pages.ulist = lambda cid, idx, oldfn: \
            util.If(cid == ucon[0],
                    oldfn(cid, idx+1),
                    oldfn(cid, idx))

    new.pages.ulist_inv = lambda cid, pn, oldfn: \
            util.If(cid == ucon[0],
                    oldfn(cid, pn)-1,
                    oldfn(cid, pn))

    new.upages[uid].available = False
    new.upages[uid].data = dt.i64(0)
    new.upages[uid].parent = block

    new.pages[block].type = dt.PAGE_TYPE_BLOCK
    new.pages[block].secrecy = secrecy_label
    new.pages[block].integrity = integrity_label
    new.pages[block].data[0] = uid

    new.pages[ucon[0]].data[sslot] = dt.PAGE_ID_INVALID
    new.pages[ucon[0]].data[islot] = dt.PAGE_ID_INVALID

    return cond, util.If(cond, new, old)


def do_alloc_thread(old, ucon, slot, sslot, islot, oslot, requested_secrecy,
                    requested_integrity, requested_ownership, tslot, gate_pagep, gate_parent_page):
    thread_secrecy = old.pages.secrecy_label(old.current)
    thread_integrity = old.pages.integrity_label(old.current)
    thread_ownership = old.pages.ownership_label(old.current)

    thread = old.pages[ucon[0]].data(slot)
    thread_local = old.pages[ucon[0]].data(tslot)

    secrecy_label = old.pages[ucon[0]].data(sslot)
    integrity_label = old.pages[ucon[0]].data(islot)
    ownership_label = old.pages[ucon[0]].data(oslot)

    gate_page = gate_pagep[0]

    cond = z3.And(
        # ucon is a CONTAINER, writable by the current thread
        old.pages.is_type(ucon, dt.PAGE_TYPE_CONTAINER),
        old.pages.can_read_write(old.current, ucon),

        z3.Distinct(slot, sslot, islot, oslot),
        z3.ULT(slot, dt.CONTAINER_NR_PAGES),
        z3.ULT(sslot, dt.CONTAINER_NR_PAGES),
        z3.ULT(islot, dt.CONTAINER_NR_PAGES),
        z3.ULT(oslot, dt.CONTAINER_NR_PAGES),

        # This is implied by the above
        z3.Distinct(secrecy_label, integrity_label, thread),

        # gate param is valid
        old.pages.is_type(gate_parent_page, dt.PAGE_TYPE_CONTAINER),
        old.pages.can_read(old.current, gate_parent_page),
        old.pages.is_type(gate_pagep, dt.PAGE_TYPE_GATE),
        old.pages.can_read(old.current, gate_pagep),
        old.pages[gate_page].parent == gate_parent_page[0],

        # TLS and ownership pages are valid container indices
        z3.ULT(tslot, dt.CONTAINER_NR_PAGES),

        # new thread's ownership must be subset of current thread's ownership
        l.is_subset(requested_ownership.has, thread_ownership),

        old.pages.is_type(thread, dt.PAGE_TYPE_UNTYPED),
        old.pages.is_type(secrecy_label, dt.PAGE_TYPE_UNTYPED),
        old.pages.is_type(integrity_label, dt.PAGE_TYPE_UNTYPED),
        old.pages.is_type(ownership_label, dt.PAGE_TYPE_UNTYPED),
        old.pages.is_type(thread_local, dt.PAGE_TYPE_BLOCK),

        # T ⊑⁺ O
        l.is_subsetx(thread_secrecy, requested_secrecy.has, thread_ownership),
        l.is_subsetx(requested_integrity.has, thread_integrity, thread_ownership),
    )

    new = old.copy()

    # Allocate ownership / secrecy / integrity label pages.
    new = alloc_label(new, ownership_label, requested_ownership, thread, dt.LABEL_TYPE_THREAD_OWNERSHIP)
    new = alloc_label(new, secrecy_label, requested_secrecy, thread, dt.LABEL_TYPE_SECRECY)
    new = alloc_label(new, integrity_label, requested_integrity, thread, dt.LABEL_TYPE_INTEGRITY)

    new.pages[thread_local].is_tls = True
    new.pages[thread_local].tls_owner = thread
    new._tls[thread] = lambda idx, oldfn: dt.i64(0)

    new.pages[thread].type = dt.i64(dt.PAGE_TYPE_THREAD)
    new.pages[thread].data[dt.i64(0)]  = ownership_label                  # ownership
    new.pages[thread].data[dt.i64(1)]  = thread_local                     # tls
    new.pages[thread].data[dt.i64(2)]  = dt.i64(dt.THREAD_STATE_RUNNABLE) # state
    # new.pages[thread].data[dt.i64(3)]  = dt.PAGE_ID_INVALID               # mm->page.id
    # new.pages[thread].data[dt.i64(4)]  = dt.i64(0)                        # mm->page.gen
    # new.pages[thread].data[dt.i64(5)]  = dt.PAGE_ID_INVALID               # mm->parent.id
    # new.pages[thread].data[dt.i64(6)]  = dt.i64(0)                        # mm->parent.gen
    new.pages[thread].data[dt.i64(7)]  = dt.i64(dt.USER_TLS_START)        # fsbase
    new.pages[thread].data[dt.i64(8)]  = dt.i64(0)                        # gsbase
    # CPU
    new.pages[thread].data[dt.i64(26)] = dt.i64(51)                       # cpu->cs
    new.pages[thread].data[dt.i64(27)] = dt.X86_RFLAGS_IF                 # cpu->rflags
    new.pages[thread].data[dt.i64(28)] = dt.i64(dt.USER_STACK_TOP)        # cpu->rsp
    new.pages[thread].data[dt.i64(29)] = dt.i64(43)                       # cpu->ss

    # Gate Entry
    new.pages[thread].data[dt.i64(3)]  = old.pages[gate_page].data(2)   # mm->page.id
    new.pages[thread].data[dt.i64(4)]  = old.pages[gate_page].data(3)   # mm->page.gen
    new.pages[thread].data[dt.i64(5)]  = old.pages[gate_page].data(4)   # mm->parent.id
    new.pages[thread].data[dt.i64(6)]  = old.pages[gate_page].data(5)   # mm->parent.gen
    new.pages[thread].data[dt.i64(17)] = old.pages[gate_page].data(12)  # cpu->r9
    new.pages[thread].data[dt.i64(18)] = old.pages[gate_page].data(11)  # cpu->r8
    new.pages[thread].data[dt.i64(20)] = old.pages[gate_page].data(10)  # cpu->rcx
    new.pages[thread].data[dt.i64(21)] = old.pages[gate_page].data(9)   # cpu->rdx
    new.pages[thread].data[dt.i64(22)] = old.pages[gate_page].data(8)   # cpu->rsi
    new.pages[thread].data[dt.i64(23)] = old.pages[gate_page].data(7)   # cpu->rdi
    new.pages[thread].data[dt.i64(25)] = old.pages[gate_page].data(6)   # cpu->rip

    new.pages[thread].secrecy = secrecy_label
    new.pages[thread].integrity = integrity_label

    new.pages[ucon[0]].data[sslot] = dt.PAGE_ID_INVALID
    new.pages[ucon[0]].data[islot] = dt.PAGE_ID_INVALID
    new.pages[ucon[0]].data[oslot] = dt.PAGE_ID_INVALID
    new.pages[ucon[0]].data[tslot] = dt.PAGE_ID_INVALID

    return cond, util.If(cond, new, old)


def do_alloc_gate(old, ucon, slot, sslot, islot, oslot, gslot,
                  requested_secrecy, requested_integrity, requested_ownership,
                  guard, pud_page, pud_parent_page, entry,
                  gatearg0, gatearg1, gatearg2):
    thread_secrecy = old.pages.secrecy_label(old.current)
    thread_integrity = old.pages.integrity_label(old.current)
    thread_ownership = old.pages.ownership_label(old.current)

    gate = old.pages[ucon[0]].data(slot)
    secrecy_label = old.pages[ucon[0]].data(sslot)
    integrity_label = old.pages[ucon[0]].data(islot)
    ownership_label = old.pages[ucon[0]].data(oslot)
    guard_label = old.pages[ucon[0]].data(gslot)

    cond = z3.And(
        z3.Distinct(slot, sslot, islot, oslot, gslot),
        z3.ULT(oslot, dt.CONTAINER_NR_PAGES),
        z3.ULT(gslot, dt.CONTAINER_NR_PAGES),

        old.pages.is_type(ucon, dt.PAGE_TYPE_CONTAINER),
        old.pages.can_read_write(old.current, ucon),

        # gate's ownership must be a subset of thread's ownership
        l.is_subset(requested_ownership.has, thread_ownership),

        old.pages.is_type(ownership_label, dt.PAGE_TYPE_UNTYPED),
        old.pages.is_type(guard_label, dt.PAGE_TYPE_UNTYPED),

        # pud param is valid
        old.pages.is_type(pud_parent_page, dt.PAGE_TYPE_CONTAINER),
        old.pages.can_read(old.current, pud_parent_page),
        old.pages.is_type(pud_page, dt.PAGE_TYPE_PUD),
        old.pages.can_read(old.current, pud_page),
        old.pages[pud_page[0]].parent == pud_parent_page[0],

        z3.ULT(slot, dt.CONTAINER_NR_PAGES),
        z3.ULT(sslot, dt.CONTAINER_NR_PAGES),
        z3.ULT(islot, dt.CONTAINER_NR_PAGES),

        old.pages.is_type(gate, dt.PAGE_TYPE_UNTYPED),
        old.pages.is_type(secrecy_label, dt.PAGE_TYPE_UNTYPED),
        old.pages.is_type(integrity_label, dt.PAGE_TYPE_UNTYPED),

        l.is_subsetx(thread_secrecy, requested_secrecy.has, thread_ownership),
        l.is_subsetx(requested_integrity.has, thread_integrity, thread_ownership),
    )

    new = old.copy()

    # Allocate ownership / secrecy / integrity label pages.
    new = alloc_label(new, secrecy_label, requested_secrecy, gate, dt.LABEL_TYPE_SECRECY)
    new = alloc_label(new, integrity_label, requested_integrity, gate, dt.LABEL_TYPE_INTEGRITY)
    new = alloc_label(new, ownership_label, requested_ownership, gate, dt.LABEL_TYPE_GATE_OWNERSHIP)
    new = alloc_label(new, guard_label, guard, gate, dt.LABEL_TYPE_GATE_GUARD)

    new.pages[gate].type = dt.i64(dt.PAGE_TYPE_GATE)
    new.pages[gate].secrecy = secrecy_label
    new.pages[gate].integrity = integrity_label
    new.pages[gate].parent = ucon[0]
    new.pages[gate].parent_slot = slot

    new.pages[gate].data[0] = ownership_label
    new.pages[gate].data[1] = guard_label
    new.pages[gate].data[2] = pud_page[0]
    new.pages[gate].data[3] = pud_page[1]
    new.pages[gate].data[4] = pud_parent_page[0]
    new.pages[gate].data[5] = pud_parent_page[1]
    new.pages[gate].data[6] = entry
    new.pages[gate].data[7] = gatearg0
    new.pages[gate].data[8] = gatearg1
    new.pages[gate].data[9] = gatearg2
    new.pages[gate].data[10] = util.i64(0) # gatearg3
    new.pages[gate].data[11] = util.i64(0) # gatearg4
    new.pages[gate].data[12] = util.i64(0) # gatearg5

    # Remove all allocated lables from conatiner
    new.pages[ucon[0]].data[sslot] = dt.PAGE_ID_INVALID
    new.pages[ucon[0]].data[islot] = dt.PAGE_ID_INVALID
    new.pages[ucon[0]].data[oslot] = dt.PAGE_ID_INVALID
    new.pages[ucon[0]].data[gslot] = dt.PAGE_ID_INVALID

    return cond, util.If(cond, new, old)


def do_alloc_directory_pud(old, ucon, slot, sslot, islot, requested_secrecy, requested_integrity):
    return alloc_page(old, ucon, slot, sslot, islot, requested_secrecy, requested_integrity, dt.PAGE_TYPE_PUD)


def do_alloc_directory_pmd(old, ucon, slot, sslot, islot, requested_secrecy, requested_integrity):
    return alloc_page(old, ucon, slot, sslot, islot, requested_secrecy, requested_integrity, dt.PAGE_TYPE_PMD)


def sys_directory_get_slot(old, usym, slot, to):
    page = (old.pages[usym[0]].data(slot*4+0), old.pages[usym[0]].data(slot*4+1))
    parent = (old.pages[usym[0]].data(slot*4+2), old.pages[usym[0]].data(slot*4+3))

    cond = z3.And(
        z3.ULT(slot, dt.DIRECTORY_NR_ENTRIES),
        z3.Or(
            old.pages.is_type(usym, dt.PAGE_TYPE_PUD),
            old.pages.is_type(usym, dt.PAGE_TYPE_PMD)),

        old.pages.can_read(old.current, usym),

        z3.ULE(to, dt.TLS_NR_SLOTS - 4),
    )

    new = old.copy()

    new.tls[to+0] = page[0]
    new.tls[to+1] = page[1]
    new.tls[to+2] = parent[0]
    new.tls[to+3] = parent[1]

    return cond, util.If(cond, new, old)


def sys_directory_link_pmd(old, upud, pudslot, ucon, slot):
    id = old.pages[ucon[0]].data(slot)

    page = (old.pages[upud[0]].data(pudslot*4+0), old.pages[upud[0]].data(pudslot*4+1))
    parent = (old.pages[upud[0]].data(pudslot*4+2), old.pages[upud[0]].data(pudslot*4+3))

    cond = z3.And(
            z3.ULT(pudslot, dt.DIRECTORY_NR_ENTRIES),
            z3.ULT(slot, dt.CONTAINER_NR_PAGES),

            old.pages.is_type(upud, dt.PAGE_TYPE_PUD),
            old.pages.can_read_write(old.current, upud),

            old.pages.is_type(ucon, dt.PAGE_TYPE_CONTAINER),
            old.pages.can_read(old.current, ucon),

            z3.Not(
                z3.And(
                    dt.page_is_valid(page[0]),
                    z3.UGT(page[1], 0),
                    dt.page_is_valid(parent[0]),
                    z3.UGT(parent[1], 0))),

            old.pages.is_type(id, dt.PAGE_TYPE_PMD),
    )

    new = old.copy()

    new.pages[upud[0]].data[pudslot*4+0] = id
    new.pages[upud[0]].data[pudslot*4+1] = old.pages[id].generation
    new.pages[upud[0]].data[pudslot*4+2] = old.pages[id].parent
    new.pages[upud[0]].data[pudslot*4+3] = old.pages[old.pages[id].parent].generation

    return cond, util.If(cond, new, old)


def do_directory_link_block(old, upmd, pmdslot, ucon, slot, pteval):
    id = old.pages[ucon[0]].data(slot)

    page = (old.pages[upmd[0]].data(pmdslot*4+0), old.pages[upmd[0]].data(pmdslot*4+1))
    parent = (old.pages[upmd[0]].data(pmdslot*4+2), old.pages[upmd[0]].data(pmdslot*4+3))

    cond = z3.And(
            z3.ULT(pmdslot, dt.DIRECTORY_NR_ENTRIES),
            z3.ULT(slot, dt.CONTAINER_NR_PAGES),

            old.pages.is_type(upmd, dt.PAGE_TYPE_PMD),
            old.pages.can_read_write(old.current, upmd),

            old.pages.is_type(ucon, dt.PAGE_TYPE_CONTAINER),
            old.pages.can_read(old.current, ucon),

            z3.Not(
                z3.And(
                    dt.page_is_valid(page[0]),
                    z3.UGT(page[1], 0),
                    dt.page_is_valid(parent[0]),
                    z3.UGT(parent[1], 0))),

            old.pages.is_type(id, dt.PAGE_TYPE_BLOCK),
    )

    new = old.copy()

    new.pages[upmd[0]].data[pmdslot*4+0] = id
    new.pages[upmd[0]].data[pmdslot*4+1] = old.pages[id].generation
    new.pages[upmd[0]].data[pmdslot*4+2] = ucon[0]
    new.pages[upmd[0]].data[pmdslot*4+3] = ucon[1]

    return cond, util.If(cond, new, old)


def sys_directory_unlink_pmd(old, upud, pudslot):
    cond = z3.And(
            z3.ULT(pudslot, dt.DIRECTORY_NR_ENTRIES),
            old.pages.is_type(upud, dt.PAGE_TYPE_PUD),
            old.pages.can_read_write(old.current, upud),
    )

    new = old.copy()

    new.pages[upud[0]].data[pudslot*4+0] = dt.PAGE_ID_INVALID
    new.pages[upud[0]].data[pudslot*4+1] = 0
    new.pages[upud[0]].data[pudslot*4+2] = dt.PAGE_ID_INVALID
    new.pages[upud[0]].data[pudslot*4+3] = 0

    return cond, util.If(cond, new, old)


def sys_directory_unlink_block(old, upmd, pmdslot):
    cond = z3.And(
            z3.ULT(pmdslot, dt.DIRECTORY_NR_ENTRIES),
            old.pages.is_type(upmd, dt.PAGE_TYPE_PMD),
            old.pages.can_read_write(old.current, upmd),
    )

    new = old.copy()

    new.pages[upmd[0]].data[pmdslot*4+0] = dt.PAGE_ID_INVALID
    new.pages[upmd[0]].data[pmdslot*4+1] = 0
    new.pages[upmd[0]].data[pmdslot*4+2] = dt.PAGE_ID_INVALID
    new.pages[upmd[0]].data[pmdslot*4+3] = 0

    return cond, util.If(cond, new, old)


def free_page(old, container, slot, type):
    id = old.pages[container[0]].data(slot)

    cond = z3.And(
        # `container` is a valid, writable container.
        old.pages.is_type(container, dt.PAGE_TYPE_CONTAINER),
        old.pages.can_read_write(old.current, container),

        # Slot is valid
        z3.ULT(slot, dt.CONTAINER_NR_PAGES),

        # Current thread can write to the object being de-allocated
        old.pages.is_type(id, type),
        old.pages.can_read_write(old.current, id),
    )

    new = old.copy()

    if type == dt.PAGE_TYPE_THREAD:
        cond = z3.And(
            cond,
            old.pages[id].data(2) == dt.THREAD_STATE_HALTED,
        )

        new.pages[old.pages.ownership(id)].type = dt.PAGE_TYPE_NONE
        new.pages.freelist_push(container[0], new.pages.ownership(id))

        new.pages[old.pages[id].secrecy].type = dt.PAGE_TYPE_NONE
        new.pages.freelist_push(container[0], old.pages[id].secrecy)

        new.pages[old.pages[id].integrity].type = dt.PAGE_TYPE_NONE
        new.pages.freelist_push(container[0], old.pages[id].integrity)

    elif type == dt.PAGE_TYPE_GATE:
        new.pages[old.pages.ownership(id)].type = dt.PAGE_TYPE_NONE
        new.pages.freelist_push(container[0], old.pages.ownership(id))

        new.pages[old.pages.gate_guard(id)].type = dt.PAGE_TYPE_NONE
        new.pages.freelist_push(container[0], old.pages.gate_guard(id))

        new.pages[old.pages[id].secrecy].type = dt.PAGE_TYPE_NONE
        new.pages.freelist_push(container[0], old.pages[id].secrecy)

        new.pages[old.pages[id].integrity].type = dt.PAGE_TYPE_NONE
        new.pages.freelist_push(container[0], old.pages[id].integrity)

    elif type == dt.PAGE_TYPE_PUD or type == dt.PAGE_TYPE_PMD:
        new.pages[old.pages[id].secrecy].type = dt.PAGE_TYPE_NONE
        new.pages.freelist_push(container[0], old.pages[id].secrecy)

        new.pages[old.pages[id].integrity].type = dt.PAGE_TYPE_NONE
        new.pages.freelist_push(container[0], old.pages[id].integrity)

    elif type == dt.PAGE_TYPE_CONTAINER:
        cond = z3.And(
            cond,
            id != container[0],
            old.pages[id].quota == 0,
            old.pages[id].uquota == 0,
            old.pages[id].qquota == 0,
        )

        new.pages[old.pages[id].secrecy].type = dt.PAGE_TYPE_NONE
        new.pages.freelist_push(container[0], old.pages[id].secrecy)

        new.pages[old.pages[id].integrity].type = dt.PAGE_TYPE_NONE
        new.pages.freelist_push(container[0], old.pages[id].integrity)

    elif type == dt.PAGE_TYPE_BLOCK:
        new.pages[old.pages[id].secrecy].type = dt.PAGE_TYPE_NONE
        new.pages.freelist_push(container[0], old.pages[id].secrecy)

        new.pages[old.pages[id].integrity].type = dt.PAGE_TYPE_NONE
        new.pages.freelist_push(container[0], old.pages[id].integrity)

        upage = old.pages[id].data(0)

        # push the page on the freelist
        new.upages[upage].next = new.pages[container[0]].unext
        new.upages[upage].parent = container[0]
        new.upages[upage].available = True
        new.pages[container[0]].unext = upage
        new.pages[container[0]].uquota += 1

        # maintain freelist
        pos = new.pages[container[0]].ulist_inv(upage)
        last = new.pages[container[0]].ulist(dt.NR_PAGES2M-1)

        new.pages.ulist = lambda cid, idx, oldfn: \
                util.If(z3.And(cid == container[0], idx == 0),
                        upage,
                        util.If(cid == container[0],
                                util.If(idx-1 == pos,
                                        last,
                                        oldfn(cid, idx-1)),
                                oldfn(cid, idx)))

        new.pages.ulist_inv = lambda cid, pn, oldfn: \
                util.If(z3.And(cid == container[0], pn == upage),
                        dt.i64(0),
                        util.If(cid == container[0],
                            util.If(pn == last,
                                    pos,
                                    oldfn(cid, pn))+1,
                            oldfn(cid, pn)))

    new.pages[id].type = dt.PAGE_TYPE_NONE
    new.pages.freelist_push(container[0], id)
    new.pages[container[0]].data[slot] = dt.PAGE_ID_INVALID

    return cond, util.If(cond, new, old)


def sys_free_gate(old, ucon, slot):
    return free_page(old, ucon, slot, dt.PAGE_TYPE_GATE)


def sys_free_block(old, ucon, slot):
    return free_page(old, ucon, slot, dt.PAGE_TYPE_BLOCK)


def sys_free_directory_pud(old, ucon, slot):
    return free_page(old, ucon, slot, dt.PAGE_TYPE_PUD)


def sys_free_directory_pmd(old, ucon, slot):
    return free_page(old, ucon, slot, dt.PAGE_TYPE_PMD)


def sys_free_thread(old, ucon, slot):
    return free_page(old, ucon, slot, dt.PAGE_TYPE_THREAD)


def sys_page_get_type(old, container, slot, to):
    cond = z3.And(
        old.pages.is_type(container, dt.PAGE_TYPE_CONTAINER),
        z3.ULT(slot, dt.CONTAINER_NR_PAGES),
        z3.ULE(to, dt.TLS_NR_SLOTS - 1),
        old.pages.can_read(old.current, container),
        dt.page_is_valid(old.pages[container[0]].data(slot)),
    )

    new = old.copy()

    id = old.pages[container[0]].data(slot)
    new.tls[to] = old.pages[id].type

    return cond, util.If(cond, new, old)


def sys_page_get_label(old, container, slot, sto, ito):
    id = old.pages[container[0]].data(slot)

    cond = z3.And(
        z3.ULT(slot, dt.CONTAINER_NR_PAGES),

        z3.ULE(sto, dt.TLS_NR_SLOTS - dt.KPAGE_SIZE),
        z3.ULE(ito, dt.TLS_NR_SLOTS - dt.KPAGE_SIZE),

        old.pages.is_type(container, dt.PAGE_TYPE_CONTAINER),
        old.pages.can_read(old.current, container),

        dt.page_is_valid(id),
        old.pages[id].type != dt.PAGE_TYPE_UNTYPED,
        old.pages[id].type != dt.PAGE_TYPE_THREAD,
    )

    new = old.copy()

    new._tls[old.current] = lambda idx, oldfn: util.If(
            z3.And(z3.UGE(idx, sto), z3.ULT(idx, sto + dt.KPAGE_SIZE)),
            old.pages[old.pages[id].secrecy].data(idx - sto),
            oldfn(idx))

    new._tls[old.current] = lambda idx, oldfn: util.If(
            z3.And(z3.UGE(idx, ito), z3.ULT(idx, ito + dt.KPAGE_SIZE)),
            old.pages[old.pages[id].integrity].data(idx - ito),
            oldfn(idx))

    return cond, util.If(cond, new, old)


def sys_page_get_name(old, container, slot, to):
    id = old.pages[container[0]].data(slot)

    cond = z3.And(
        old.pages.is_type(container, dt.PAGE_TYPE_CONTAINER),
        z3.ULT(slot, dt.CONTAINER_NR_PAGES),
        z3.ULE(to, dt.TLS_NR_SLOTS - dt.PAGE_NAME_LEN),
        old.pages.can_read(old.current, container),

        dt.page_is_valid(id),
        z3.Or(
            old.pages[id].type == dt.PAGE_TYPE_UNTYPED,
            old.pages.can_read(old.current, id)),
    )

    new = old.copy()

    new._tls[old.current] = lambda idx, oldfn: util.If(
            z3.And(z3.UGE(idx, to), z3.ULT(idx, to + dt.PAGE_NAME_LEN)),
            old.pages[id].name(idx - to),
            oldfn(idx))

    return cond, util.If(cond, new, old)


def sys_page_set_name(old, container, slot, frm):
    id = old.pages[container[0]].data(slot)

    cond = z3.And(
        old.pages.is_type(container, dt.PAGE_TYPE_CONTAINER),
        z3.ULT(slot, dt.CONTAINER_NR_PAGES),
        z3.ULE(frm, dt.TLS_NR_SLOTS - dt.PAGE_NAME_LEN),
        old.pages.can_read(old.current, container),

        dt.page_is_valid(id),
        old.pages[id].type != dt.PAGE_TYPE_UNTYPED,
        old.pages.can_read_write(old.current, id),
    )

    new = old.copy()

    for idx in range(dt.PAGE_NAME_LEN):
        new.pages[id].name[idx] = old.tls(frm + idx)

    return cond, util.If(cond, new, old)


def sys_page_get_metadata(old, container, slot, to):
    id = old.pages[container[0]].data(slot)

    cond = z3.And(
        old.pages.is_type(container, dt.PAGE_TYPE_CONTAINER),
        z3.ULT(slot, dt.CONTAINER_NR_PAGES),
        z3.ULE(to, dt.TLS_NR_SLOTS - dt.PAGE_METADATA_LEN),
        old.pages.can_read(old.current, container),

        dt.page_is_valid(id),
        z3.Or(
            old.pages[id].type == dt.PAGE_TYPE_UNTYPED,
            old.pages.can_read(old.current, id)),
    )

    new = old.copy()

    new._tls[old.current] = lambda idx, oldfn: util.If(
            z3.And(z3.UGE(idx, to), z3.ULT(idx, to + dt.PAGE_METADATA_LEN)),
            old.pages[id].metadata(idx - to),
            oldfn(idx))

    return cond, util.If(cond, new, old)


def sys_page_set_metadata(old, container, slot, frm):
    id = old.pages[container[0]].data(slot)

    cond = z3.And(
        old.pages.is_type(container, dt.PAGE_TYPE_CONTAINER),
        z3.ULT(slot, dt.CONTAINER_NR_PAGES),
        z3.ULE(frm, dt.TLS_NR_SLOTS - dt.PAGE_METADATA_LEN),
        old.pages.can_read(old.current, container),

        dt.page_is_valid(id),
        old.pages[id].type != dt.PAGE_TYPE_UNTYPED,
        old.pages.can_read_write(old.current, id),
    )

    new = old.copy()

    for idx in range(dt.PAGE_METADATA_LEN):
        new.pages[id].metadata[idx] = old.tls(frm + idx)

    return cond, util.If(cond, new, old)


def do_gate_enter(old, container, slot, requested_ownership, arg):
    thread_ownership = old.pages.ownership_label(old.current)

    gate = old.pages[container[0]].data(slot)
    gate_ownership = old.pages.ownership_label(gate)
    gate_guard = old.pages.label[old.pages.gate_guard(gate)].label

    cond = z3.And(
        old.pages.is_type(container, dt.PAGE_TYPE_CONTAINER),
        old.pages.can_read(old.current, container),
        z3.ULT(slot, dt.CONTAINER_NR_PAGES),

        old.pages.is_type(gate, dt.PAGE_TYPE_GATE),
        old.pages.can_read(old.current, gate),

        # Thread's ownership must be a superset of the gate's guard label
        l.is_subset(gate_guard, thread_ownership),

        # new thread's ownership must be subset of union of old ownership and gate's ownership
        l.is_subsetx(requested_ownership.has, gate_ownership, thread_ownership),
    )

    new = old.copy()

    ownership_pn = old.pages.ownership(old.current)

    set_label(new, ownership_pn, requested_ownership)

    new.pages[old.current].data[dt.i64(3)]  = old.pages[gate].data(2)   # mm->page.id
    new.pages[old.current].data[dt.i64(4)]  = old.pages[gate].data(3)   # mm->page.gen
    new.pages[old.current].data[dt.i64(5)]  = old.pages[gate].data(4)   # mm->parent.id
    new.pages[old.current].data[dt.i64(6)]  = old.pages[gate].data(5)   # mm->parent.gen
    new.pages[old.current].data[dt.i64(17)] = old.pages[gate].data(12)  # cpu->r9
    new.pages[old.current].data[dt.i64(18)] = old.pages[gate].data(11)  # cpu->r8
    new.pages[old.current].data[dt.i64(20)] = old.pages[gate].data(10)  # cpu->rcx
    new.pages[old.current].data[dt.i64(21)] = arg                       # cpu->rdx
    new.pages[old.current].data[dt.i64(22)] = old.pages[gate].data(8)   # cpu->rsi
    new.pages[old.current].data[dt.i64(23)] = old.pages[gate].data(7)   # cpu->rdi
    new.pages[old.current].data[dt.i64(25)] = old.pages[gate].data(6)   # cpu->rip

    return cond, util.If(cond, new, old)


def sys_gate_get_label(old, container, slot, sto, ito, oto):
    id = old.pages[container[0]].data(slot)

    cond = z3.And(
        z3.ULT(slot, dt.CONTAINER_NR_PAGES),

        z3.ULE(sto, dt.TLS_NR_SLOTS - dt.KPAGE_SIZE),
        z3.ULE(ito, dt.TLS_NR_SLOTS - dt.KPAGE_SIZE),
        z3.ULE(oto, dt.TLS_NR_SLOTS - dt.KPAGE_SIZE),

        old.pages.is_type(container, dt.PAGE_TYPE_CONTAINER),
        old.pages.can_read(old.current, container),

        dt.page_is_valid(id),
        old.pages[id].type == dt.PAGE_TYPE_GATE,
    )

    new = old.copy()

    new._tls[old.current] = lambda idx, oldfn: util.If(
            z3.And(z3.UGE(idx, sto), z3.ULT(idx, sto + dt.KPAGE_SIZE)),
            old.pages[old.pages[id].secrecy].data(idx - sto),
            oldfn(idx))

    new._tls[old.current] = lambda idx, oldfn: util.If(
            z3.And(z3.UGE(idx, ito), z3.ULT(idx, ito + dt.KPAGE_SIZE)),
            old.pages[old.pages[id].integrity].data(idx - ito),
            oldfn(idx))

    new._tls[old.current] = lambda idx, oldfn: util.If(
            z3.And(z3.UGE(idx, oto), z3.ULT(idx, oto + dt.KPAGE_SIZE)),
            old.pages[old.pages.ownership(id)].data(idx - oto),
            oldfn(idx))

    return cond, util.If(cond, new, old)


def sys_thread_get_state(old, container, slot, to):
    id = old.pages[container[0]].data(slot)

    cond = z3.And(
        z3.ULT(slot, dt.CONTAINER_NR_PAGES),
        z3.ULE(to, dt.TLS_NR_SLOTS - 1),

        old.pages.is_type(container, dt.PAGE_TYPE_CONTAINER),
        old.pages.can_read(old.current, container),

        dt.page_is_valid(id),
        old.pages[id].type == dt.PAGE_TYPE_THREAD,
        old.pages.can_read(old.current, id),
    )

    new = old.copy()
    new.tls[to] = old.pages[id].data(2)
    return cond, util.If(cond, new, old)


def sys_self_get(old, to):
    cond = z3.And(
        z3.ULE(to, dt.TLS_NR_SLOTS - 4),
    )

    new = old.copy()

    new.tls[to+0] = old.current
    new.tls[to+1] = old.pages[old.current].generation
    new.tls[to+2] = old.pages[old.current].parent
    new.tls[to+3] = old.pages[old.pages[old.current].parent].generation
    return cond, util.If(cond, new, old)


def sys_self_get_pud(old, to):
    cond = z3.And(
        z3.ULE(to, dt.TLS_NR_SLOTS - 4),
    )

    new = old.copy()
    new.tls[to+0] = old.pages[old.current].data(3)
    new.tls[to+1] = old.pages[old.current].data(4)
    new.tls[to+2] = old.pages[old.current].data(5)
    new.tls[to+3] = old.pages[old.current].data(6)
    return cond, util.If(cond, new, old)


def sys_self_get_label(old, sto, ito, oto):
    id = old.current

    cond = z3.And(
        z3.ULE(sto, dt.TLS_NR_SLOTS - dt.KPAGE_SIZE),
        z3.ULE(ito, dt.TLS_NR_SLOTS - dt.KPAGE_SIZE),
        z3.ULE(oto, dt.TLS_NR_SLOTS - dt.KPAGE_SIZE),
    )

    new = old.copy()

    new._tls[old.current] = lambda idx, oldfn: util.If(
            z3.And(z3.UGE(idx, sto), z3.ULT(idx, sto + dt.KPAGE_SIZE)),
            old.pages[old.pages[id].secrecy].data(idx - sto),
            oldfn(idx))

    new._tls[old.current] = lambda idx, oldfn: util.If(
            z3.And(z3.UGE(idx, ito), z3.ULT(idx, ito + dt.KPAGE_SIZE)),
            old.pages[old.pages[id].integrity].data(idx - ito),
            oldfn(idx))

    new._tls[old.current] = lambda idx, oldfn: util.If(
            z3.And(z3.UGE(idx, oto), z3.ULT(idx, oto + dt.KPAGE_SIZE)),
            old.pages[old.pages.ownership(id)].data(idx - oto),
            oldfn(idx))

    return cond, util.If(cond, new, old)


def do_self_set_label(old, requested_secrecy, requested_integrity, requested_ownership):
    thread_secrecy = old.pages.secrecy_label(old.current)
    thread_integrity = old.pages.integrity_label(old.current)
    thread_ownership = old.pages.ownership_label(old.current)

    cond = z3.And(
        l.is_subsetx(thread_secrecy, requested_secrecy.has, thread_ownership),
        l.is_subsetx(requested_integrity.has, thread_integrity, thread_ownership),
        l.is_subset(requested_ownership.has, thread_ownership),
    )

    new = old.copy()

    secrecy_pn = old.pages[old.current].secrecy
    integrity_pn = old.pages[old.current].integrity
    ownership_pn = old.pages.ownership(old.current)

    set_label(new, secrecy_pn, requested_secrecy)
    set_label(new, integrity_pn, requested_integrity)
    set_label(new, ownership_pn, requested_ownership)

    return cond, util.If(cond, new, old)


def thread_handle_pagefault(old, pgd, pud, pmd, error):
    write = (error & 0x2) != 0
    perm = dt.PTE_PRESENT | dt.PTE_USER | dt.PTE_PSE | util.If(write, dt.PTE_RW, 0)

    mm_pud = (old.pages[old.current].data(3),
              old.pages[old.current].data(4))
    mm_pud_parent = (old.pages[old.current].data(5),
                     old.pages[old.current].data(6))

    mm_pmd = (old.pages[mm_pud[0]].data(pud * 4 + 0),
              old.pages[mm_pud[0]].data(pud * 4 + 1))
    mm_pmd_parent = (old.pages[mm_pud[0]].data(pud * 4 + 2),
                     old.pages[mm_pud[0]].data(pud * 4 + 3))

    mm_block = (old.pages[mm_pmd[0]].data(pmd * 4 + 0),
                old.pages[mm_pmd[0]].data(pmd * 4 + 1))
    mm_block_parent = (old.pages[mm_pmd[0]].data(pmd * 4 + 2),
                       old.pages[mm_pmd[0]].data(pmd * 4 + 3))

    cond = z3.And(
            pgd == 0,

            # Validate PUD
            old.pages.is_type(mm_pud_parent, dt.PAGE_TYPE_CONTAINER),
            # old.pages.can_read(old.current, mm_pud_parent),
            old.pages.is_type(mm_pud, dt.PAGE_TYPE_PUD),
            old.pages.can_read(old.current, mm_pud),
            old.pages[mm_pud[0]].parent == mm_pud_parent[0],

            # Validate PMD
            old.pages.is_type(mm_pmd_parent, dt.PAGE_TYPE_CONTAINER),
            # old.pages.can_read(old.current, mm_pmd_parent),
            old.pages.is_type(mm_pmd, dt.PAGE_TYPE_PMD),
            old.pages.can_read(old.current, mm_pmd),
            old.pages[mm_pmd[0]].parent == mm_pmd_parent[0],

            # Validate BLOCK
            old.pages.is_type(mm_block_parent, dt.PAGE_TYPE_CONTAINER),
            # old.pages.can_read(old.current, mm_block_parent),
            old.pages.is_type(mm_block, dt.PAGE_TYPE_BLOCK),
            old.pages.can_read(old.current, mm_block),
            old.pages[mm_block[0]].parent == mm_block_parent[0],

            util.Implies(write, old.pages.can_write(old.current, mm_block)),
            # util.If(write,
            #     old.pages.can_write(old.current, mm_block),
            #     z3.BoolVal(True)),
    )

    new = old.copy()

    return cond, util.If(cond, new, old)


def sched_next(old):
    new = old.copy()
    new.current_slot = util.If(new.current_slot + 1 == dt.SCHED_NR_QUANTA,
                               util.i64(0), new.current_slot + 1)

    return z3.BoolVal(True), new
