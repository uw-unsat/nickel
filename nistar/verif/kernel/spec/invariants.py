import z3

from libirpy import solver
from libirpy import util

import datatypes as dt


def impl_invariants_c(ctx):
    conj = []

    pn = util.FreshBitVec('pn', dt.uint64_t)

    try:
        old_solver = ctx.solver
        old_globals = ctx.globals

        def implies(ctx, a, b):
            return z3.Implies(a, b)

        def and_(ctx, *args):
            return z3.And(*args)

        def or_(ctx, *args):
            return z3.Or(*args)

        def not_(ctx, *args):
            return z3.Not(*args)

        ctx.globals['@implies'] = implies
        ctx.globals['@not'] = not_
        ctx.globals['@and2'] = and_
        ctx.globals['@and3'] = and_
        ctx.globals['@and4'] = and_
        ctx.globals['@and5'] = and_
        ctx.globals['@and6'] = and_
        ctx.globals['@and7'] = and_
        ctx.globals['@and8'] = and_
        ctx.globals['@and9'] = and_
        ctx.globals['@or2'] = or_
        ctx.globals['@or3'] = or_
        ctx.globals['@or4'] = or_

        ctx.solver = solver.Solver()
        ctx.solver.add(z3.BoolVal(False))

        conj.append(ctx.call('@root_container_id_valid'))
        conj.append(ctx.call('@current_thread_valid'))
        conj.append(ctx.call('@current_thread_thread'))
        conj.append(z3.ForAll([pn], ctx.call('@secrecy_integrity_valid', pn)))

    finally:
        ctx.solver = old_solver
        ctx.globals = old_globals

    return z3.And(*conj)


def page_is_type(ctx, id, type):
    return z3.And(dt.page_is_valid(id),
                  util.global_field_element(ctx, '@pages', 'type', id) == type)


def kpage_is_type(ctx, id, gen, type):
    return z3.And(dt.page_is_valid(id),
                  util.global_field_element(ctx, '@pages', 'generation', id) == gen,
                  util.global_field_element(ctx, '@pages', 'type', id) == type)


def impl_invariants_py(ctx):
    conj = []

    pn = util.FreshBitVec('pn', dt.page_id_t)
    slot = util.FreshBitVec('slot', dt.size_t)

    # Current thread and root container are valid pages with correct type
    conj.append(page_is_type(ctx, util.global_value(ctx, '@root_container_id'), dt.PAGE_TYPE_CONTAINER))
    conj.append(page_is_type(ctx, ctx.globals['#current_thread'], dt.PAGE_TYPE_THREAD))
    # Current thread is not halted
    conj.append(util.global_to_uf_dict(ctx, '@pages_data')[()](util.i64(0), ctx.globals['#current_thread'], 2) != dt.THREAD_STATE_HALTED)

    # Page type is valid
    conj.append(z3.ForAll([pn], z3.Implies(
        dt.page_is_valid(pn),
        z3.ULT(util.global_field_element(ctx, '@pages', 'type', pn), dt.PAGE_TYPE_LAST))))

    # blocks have valid 2m page link (field 0)
    conj.append(z3.ForAll([pn], z3.Implies(
        page_is_type(ctx, pn, dt.PAGE_TYPE_BLOCK),
        z3.ULT(
            util.global_to_uf_dict(ctx, '@pages_data')[()](util.i64(0), pn, 0), dt.NR_PAGES2M))))
    # blocks can not link to unallocated pages
    conj.append(z3.ForAll([pn], z3.Implies(
        page_is_type(ctx, pn, dt.PAGE_TYPE_BLOCK),
        z3.ULT(
            util.global_to_uf_dict(ctx, '@pages_data')[()](util.i64(0), pn, 0), dt.NR_PAGES2M))))

    # threads have valid ownership page (field 0)
    conj.append(z3.ForAll([pn], z3.Implies(
        page_is_type(ctx, pn, dt.PAGE_TYPE_THREAD),
        page_is_type(ctx, util.global_to_uf_dict(ctx, '@pages_data')[()](util.i64(0), pn, 0), dt.PAGE_TYPE_LABEL))))

    # threads have valid tls page (field 1)
    conj.append(z3.ForAll([pn], z3.Implies(
        page_is_type(ctx, pn, dt.PAGE_TYPE_THREAD),
        page_is_type(ctx, util.global_to_uf_dict(ctx, '@pages_data')[()](util.i64(0), pn, 1), dt.PAGE_TYPE_BLOCK))))

    # gates have valid ownership page (field 0)
    conj.append(z3.ForAll([pn], z3.Implies(
        page_is_type(ctx, pn, dt.PAGE_TYPE_GATE),
        page_is_type(ctx, util.global_to_uf_dict(ctx, '@pages_data')[()](util.i64(0), pn, 0), dt.PAGE_TYPE_LABEL))))

    # gates have valid guard page (field 1)
    conj.append(z3.ForAll([pn], z3.Implies(
        page_is_type(ctx, pn, dt.PAGE_TYPE_GATE),
        page_is_type(ctx, util.global_to_uf_dict(ctx, '@pages_data')[()](util.i64(0), pn, 1), dt.PAGE_TYPE_LABEL))))

    # Every typed page has a valid secrecy and integrity ptr
    conj.append(z3.ForAll([pn], z3.Implies(
        z3.And(dt.page_is_valid(pn),
               z3.UGT(util.global_field_element(ctx, '@pages', 'type', pn), dt.PAGE_TYPE_LABEL)),
        z3.And(
            # secrecy and integrity pages are not the same
            z3.Distinct(
                util.global_field_element(ctx, '@pages', 'secrecy', pn),
                util.global_field_element(ctx, '@pages', 'integrity', pn)),
            page_is_type(ctx, util.global_field_element(ctx, '@pages', 'secrecy', pn), dt.PAGE_TYPE_LABEL),
            page_is_type(ctx, util.global_field_element(ctx, '@pages', 'integrity', pn), dt.PAGE_TYPE_LABEL)))))

    # Every object has a valid parent / slot
    conj.append(z3.ForAll([pn], z3.Implies(
        z3.And(dt.page_is_valid(pn),
               dt.page_type_normal(util.global_field_element(ctx, '@pages', 'type', pn))),
        page_is_type(ctx, util.global_field_element(ctx, '@pages', 'c_parent', pn), dt.PAGE_TYPE_CONTAINER))))

    # Every object in a container has "backlink"
    conj.append(z3.ForAll([pn, slot], z3.Implies(
        z3.And(
            dt.page_is_valid(pn),
            z3.ULT(slot, dt.CONTAINER_NR_PAGES),
            util.global_field_element(ctx, '@pages', 'type', pn) == dt.PAGE_TYPE_CONTAINER,
            dt.page_is_valid(util.global_to_uf_dict(ctx, '@pages_data')[()](util.i64(0), pn, slot))),
        z3.And(
            # only "normal" pages can appear in containers
            dt.page_type_normal(
                util.global_field_element(ctx, '@pages', 'type',
                    util.global_to_uf_dict(ctx, '@pages_data')[()](util.i64(0), pn, slot))),

            # c_parent points back to the container
            util.global_field_element(ctx, '@pages', 'c_parent',
                util.global_to_uf_dict(ctx, '@pages_data')[()](util.i64(0), pn, slot)) == pn,
            util.global_field_element(ctx, '@pages', 'c_parent_slot',
                util.global_to_uf_dict(ctx, '@pages_data')[()](util.i64(0), pn, slot)) == slot,
            ))))

    qid = util.FreshBitVec('qid', dt.quantum_id_t)

    conj.append(z3.ULT(util.global_value(ctx, '@current_ptr'), dt.SCHED_NR_QUANTA))

    # Every container ptr in quantum is a valid container
    conj.append(z3.ForAll([qid], z3.Implies(
        z3.ULT(qid, dt.SCHED_NR_QUANTA),
        page_is_type(ctx,
            util.global_field_element(ctx, '@time', 'container', 0, qid), dt.PAGE_TYPE_CONTAINER),
            )))

    return z3.And(*conj)


impl_invariants = impl_invariants_py


def spec_invariants_label_pack(conj, state):
    pn = util.FreshBitVec('pack.pn', dt.page_id_t)
    slot = util.FreshBitVec('pack.slot', dt.uint64_t)

    idx = state.pages.label.idx
    data = state.pages.label.data
    has = state.pages.label.has
    rawdata = state.pages.data

    conj.append(z3.ForAll([pn, slot], z3.Implies(
        z3.And(
            state.pages[pn].type == dt.PAGE_TYPE_LABEL,
            z3.ULT(slot, dt.LABEL_NR_TAGS)),
        z3.Concat(rawdata(pn, slot * 2 + 1), rawdata(pn, slot * 2)) == data(pn, slot))))

    # For every tag in data, label `has` that tag.
    # except for holes in the array for TAG_INVALID
    slot = util.FreshBitVec('pack.slot', dt.uint64_t)
    conj.append(z3.ForAll([pn, slot], z3.Implies(
        z3.And(
            state.pages[pn].type == dt.PAGE_TYPE_LABEL,
            z3.ULT(slot, dt.LABEL_NR_TAGS),
            data(pn, slot) != dt.TAG_INVALID),
        has(pn, data(pn, slot)))))

    # idx is always valid
    tag = util.FreshBitVec('pack.tag', dt.tag_t)
    conj.append(z3.ForAll([tag, pn], z3.Implies(
        z3.And(
            state.pages[pn].type == dt.PAGE_TYPE_LABEL,
            has(pn, tag)),
        z3.ULT(idx(pn, tag), dt.LABEL_NR_TAGS))))

    # has(tag) (by-)implies idx inverses data
    conj.append(z3.ForAll([tag, pn], z3.Implies(
        z3.And(
            state.pages[pn].type == dt.PAGE_TYPE_LABEL,
            tag != dt.TAG_INVALID),
        has(pn, tag) == (data(pn, idx(pn, tag)) == tag))))

    # no label contains TAG_INVALID
    conj.append(z3.ForAll([pn], z3.Implies(
        state.pages[pn].type == dt.PAGE_TYPE_LABEL,
        z3.Not(has(pn, dt.TAG_INVALID)))))


def spec_invariant_container_object_unique(conj, state):
    """Emit invariants that there is only one hardlink to an object (a unique
    container, slot pair)"""

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


def spec_invariant_untyped_zero(conj, state):
    id = util.FreshBitVec('id', dt.page_id_t)
    idx = util.FreshBitVec('idx', dt.size_t)

    # data is zero
    conj.append(z3.ForAll([id, idx], z3.Implies(
        z3.And(
            dt.page_is_valid(id),
            state.pages[id].type == dt.PAGE_TYPE_UNTYPED,
            z3.ULT(idx, dt.KPAGE_SIZE)),
        state.pages[id].data(idx) == 0)))

    # name is zero
    conj.append(z3.ForAll([id, idx], z3.Implies(
        z3.And(
            dt.page_is_valid(id),
            state.pages[id].type == dt.PAGE_TYPE_UNTYPED,
            z3.ULT(idx, dt.PAGE_NAME_LEN)),
        state.pages[id].name(idx) == 0)))

    # metadata is zero
    conj.append(z3.ForAll([id, idx], z3.Implies(
        z3.And(
            dt.page_is_valid(id),
            state.pages[id].type == dt.PAGE_TYPE_UNTYPED,
            z3.ULT(idx, dt.PAGE_METADATA_LEN)),
        state.pages[id].metadata(idx) == 0)))


def spec_invariant_time(conj, state):
    conj.append(z3.ULT(state.current_slot, dt.SCHED_NR_QUANTA))
    q = util.FreshBitVec('q', dt.quantum_id_t)
    conj.append(z3.ForAll([q],
        z3.Implies(
            z3.ULT(q, dt.SCHED_NR_QUANTA),
            z3.And(
                dt.page_is_valid(state.time[q].thread),
                dt.page_is_valid(state.time[q].container),
                state.pages[state.time[q].container].type == dt.PAGE_TYPE_CONTAINER))))


def spec_invariants(state):
    conj = []

    id = util.FreshBitVec('id', dt.page_id_t)

    conj.append(dt.page_is_valid(state.current))
    conj.append(state.pages[state.current].type == dt.PAGE_TYPE_THREAD)

    conj.append(dt.page_is_valid(state.idle))
    conj.append(state.pages[state.idle].type == dt.PAGE_TYPE_THREAD)
    conj.append(state.pages[state.idle].data(2) == dt.THREAD_STATE_RUNNABLE)

    conj.append(dt.page_is_valid(state.root_container_id))
    conj.append(state.pages[state.root_container_id].type == dt.PAGE_TYPE_CONTAINER)

    conj.append(z3.ForAll([id], z3.Implies(
        dt.page_is_valid(id),
        z3.ULT(state.pages[id].type, dt.PAGE_TYPE_LAST))))

    # Every "normal" object has valid label pages
    conj.append(z3.ForAll([id], z3.Implies(
        z3.And(
            dt.page_is_valid(id),
            z3.UGT(state.pages[id].type, dt.PAGE_TYPE_LABEL)),
        z3.And(
            dt.page_is_valid(state.pages[id].secrecy),
            dt.page_is_valid(state.pages[id].integrity),
            state.pages[state.pages[id].secrecy].type == dt.PAGE_TYPE_LABEL,
            state.pages[state.pages[id].integrity].type == dt.PAGE_TYPE_LABEL))))

    # Threads have valid ownership
    conj.append(z3.ForAll([id], z3.Implies(
        z3.And(
            dt.page_is_valid(id),
            state.pages[id].type == dt.PAGE_TYPE_THREAD),
        z3.And(
            dt.page_is_valid(state.pages.ownership(id)),
            state.pages[state.pages.ownership(id)].type == dt.PAGE_TYPE_LABEL))))

    # Gates have valid ownership
    conj.append(z3.ForAll([id], z3.Implies(
        z3.And(
            dt.page_is_valid(id),
            state.pages[id].type == dt.PAGE_TYPE_GATE),
        z3.And(
            dt.page_is_valid(state.pages.ownership(id)),
            state.pages[state.pages.ownership(id)].type == dt.PAGE_TYPE_LABEL))))

    # Gates have valid guard label
    conj.append(z3.ForAll([id], z3.Implies(
        z3.And(
            dt.page_is_valid(id),
            state.pages[id].type == dt.PAGE_TYPE_GATE),
        z3.And(
            dt.page_is_valid(state.pages.gate_guard(id)),
            state.pages[state.pages.gate_guard(id)].type == dt.PAGE_TYPE_LABEL))))

    # All non-container types have zero quota
    conj.append(z3.ForAll([id], z3.Implies(
        z3.And(
            dt.page_is_valid(id),
            state.pages[id].type != dt.PAGE_TYPE_CONTAINER),
        state.pages[id].quota == 0)))

    spec_invariant_container_object_unique(conj, state)
    spec_invariant_untyped_zero(conj, state)
    # spec_invariant_label_unique(conj, state)
    # spec_invariants_label_pack(conj, state)
    # spec_invariants_label_unique(conj, state)
    spec_invariant_time(conj, state)

    return z3.And(*conj)


def spec_invariant_label_unique_inv(conj, state):
    id = util.FreshBitVec('id', dt.page_id_t)

    conj.append(z3.ForAll([id], z3.Implies(
        z3.And(
            dt.page_is_valid(id),
            state.pages[id].type == dt.PAGE_TYPE_LABEL),
        z3.And(
            dt.page_is_valid(state.pages[id].label_owner),
            z3.UGT(state.pages[state.pages[id].label_owner].type, dt.PAGE_TYPE_LABEL),
            z3.ULT(state.pages[state.pages[id].label_owner].type, dt.PAGE_TYPE_LAST),
            z3.ULT(state.pages[id].label_type, dt.LABEL_TYPE_LAST),

            # label type secrecy
            z3.Implies(state.pages[id].label_type == dt.LABEL_TYPE_SECRECY,
                       state.pages[state.pages[id].label_owner].secrecy == id),

            # label type integrity
            z3.Implies(state.pages[id].label_type == dt.LABEL_TYPE_INTEGRITY,
                       state.pages[state.pages[id].label_owner].integrity == id),

            # label type thread ownership
            z3.Implies(state.pages[id].label_type == dt.LABEL_TYPE_THREAD_OWNERSHIP,
                z3.And(state.pages[state.pages[id].label_owner].type == dt.PAGE_TYPE_THREAD,
                       state.pages.ownership(state.pages[id].label_owner) == id)),

            # label type gate ownership
            z3.Implies(state.pages[id].label_type == dt.LABEL_TYPE_GATE_OWNERSHIP,
                z3.And(state.pages[state.pages[id].label_owner].type == dt.PAGE_TYPE_GATE,
                       state.pages.ownership(state.pages[id].label_owner) == id)),

            # label type gate guard
            z3.Implies(state.pages[id].label_type == dt.LABEL_TYPE_GATE_GUARD,
                z3.And(state.pages[state.pages[id].label_owner].type == dt.PAGE_TYPE_GATE,
                       state.pages.gate_guard(state.pages[id].label_owner) == id)),
    ))))
