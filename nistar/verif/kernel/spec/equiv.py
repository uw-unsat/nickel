import sys
import z3

import libirpy.util as util

import invariants
import datatypes as dt
import lemmas


def __kpage(ctx, identifier):
    gen = util.global_field_element(ctx, '@pages', 'generation', identifier)
    return z3.Concat(gen, identifier)


def label_equiv(conj, ctx, kernelstate):
    id = util.FreshBitVec('id', dt.page_id_t)
    tag = util.FreshBitVec('tag', dt.tag_t)

    conj.append(z3.ForAll([id, tag], z3.Implies(
        dt.page_is_valid(id),
        ctx.globals['#label'].has(id, tag) ==
            kernelstate.pages.label[id].label(tag))))


def pages_data_equiv(conj, ctx, kernelstate):
    id = util.FreshBitVec('id', dt.uint64_t)
    idx = util.FreshBitVec('idx', dt.uint64_t)

    conj.append(z3.ForAll([id, idx], z3.Implies(
        z3.And(
            dt.page_is_valid(id),
            z3.ULT(idx, dt.KPAGE_SIZE)),
        util.global_to_uf_dict(ctx, '@pages_data')[()](util.i64(0), id, idx) ==
        kernelstate.pages[id].data(idx))))


def pages_equiv(conj, ctx, kernelstate):
    id = util.FreshBitVec('id', 64)
    idx = util.FreshBitVec('idx', dt.uint64_t)

    conj.append(z3.ForAll([id], z3.Implies(
        dt.page_is_valid(id),
        kernelstate.pages[id].generation ==
        util.global_field_element(ctx, '@pages', 'generation', id))))

    conj.append(z3.ForAll([id], z3.Implies(
        dt.page_is_valid(id),
        kernelstate.pages[id].type ==
        util.global_field_element(ctx, '@pages', 'type', id))))

    # Secrecy & integrity
    conj.append(z3.ForAll([id], z3.Implies(
        dt.page_is_valid(id),
        kernelstate.pages[id].secrecy ==
        util.global_field_element(ctx, '@pages', 'secrecy', id))))

    conj.append(z3.ForAll([id], z3.Implies(
        dt.page_is_valid(id),
        kernelstate.pages[id].integrity ==
        util.global_field_element(ctx, '@pages', 'integrity', id))))

    # name
    conj.append(z3.ForAll([id, idx], z3.Implies(
        z3.And(
            dt.page_is_valid(id),
            z3.ULT(idx, dt.PAGE_NAME_LEN)),
        kernelstate.pages[id].name(idx) ==
        util.global_field_element(ctx, '@pages', 'name', id, idx))))

    # metadata
    conj.append(z3.ForAll([id, idx], z3.Implies(
        z3.And(
            dt.page_is_valid(id),
            z3.ULT(idx, dt.PAGE_METADATA_LEN)),
        kernelstate.pages[id].metadata(idx) ==
        util.global_field_element(ctx, '@pages', 'metadata', id, idx))))

    # parent
    conj.append(z3.ForAll([id], z3.Implies(
        dt.page_is_valid(id),
        kernelstate.pages[id].parent ==
        util.global_field_element(ctx, '@pages', 'c_parent', id))))

    conj.append(z3.ForAll([id], z3.Implies(
        dt.page_is_valid(id),
        kernelstate.pages[id].parent_slot ==
        util.global_field_element(ctx, '@pages', 'c_parent_slot', id))))

    # Tag counter
    conj.append(z3.ForAll([id], z3.Implies(
        dt.page_is_valid(id),
        kernelstate.pages[id].tag_counter ==
        util.global_field_element(ctx, '@pages', 'tag_counter', id))))

    # freelist
    conj.append(z3.ForAll([id], z3.Implies(
        dt.page_is_valid(id),
        kernelstate.pages[id].next ==
        util.global_field_element(ctx, '@pages', [None, None, 'freelist_next'], id))))

    # ufreelist
    conj.append(z3.ForAll([id], z3.Implies(
        dt.page_is_valid(id),
        kernelstate.pages[id].unext ==
        util.global_field_element(ctx, '@pages', [None, None, 'ufreelist_next'], id))))

    # quota & uquota
    conj.append(z3.ForAll([id], z3.Implies(
        dt.page_is_valid(id),
        kernelstate.pages[id].quota ==
        util.global_field_element(ctx, '@pages', [None, None, 'c_quota'], id))))

    conj.append(z3.ForAll([id], z3.Implies(
        dt.page_is_valid(id),
        kernelstate.pages[id].uquota ==
        util.global_field_element(ctx, '@pages', [None, None, 'c_uquota'], id))))

    conj.append(z3.ForAll([id], z3.Implies(
        dt.page_is_valid(id),
        kernelstate.pages[id].qquota ==
        util.global_field_element(ctx, '@pages', [None, None, 'c_qquota'], id))))

    # invalid pages are RESERVED
    conj.append(z3.ForAll([id], z3.Implies(
        z3.Not(dt.page_is_valid(id)),
        kernelstate.pages[id].type == dt.PAGE_TYPE_RESERVED)))

    # data equiv
    pages_data_equiv(conj, ctx, kernelstate)

    # label equiv
    label_equiv(conj, ctx, kernelstate)


def upages_equiv(conj, ctx, kernelstate):
    id = util.FreshBitVec('id', 64)
    idx = util.FreshBitVec('idx', dt.uint64_t)

    conj.append(z3.ForAll([id], z3.Implies(
        dt.upage_is_valid(id),
        kernelstate.upages[id].available ==
        (util.global_field_element(ctx, '@page2ms', 'available', id) != 0))))

    conj.append(z3.ForAll([id], z3.Implies(
        dt.upage_is_valid(id),
        kernelstate.upages[id].next ==
        util.global_field_element(ctx, '@page2ms', 'next', id))))

    conj.append(z3.ForAll([id, idx], z3.Implies(
        z3.And(
            dt.upage_is_valid(id),
            z3.ULT(idx, dt.PAGE2M_SIZE)),
        kernelstate.upages[id].data(idx) ==
        util.global_to_uf_dict(ctx, '@page2ms_data')[()](util.i64(0), id, idx))))


def time_equiv(conj, ctx, kernelstate):
    id = util.FreshBitVec('tid', dt.quantum_id_t)

    conj.append(z3.ForAll([id], z3.Implies(
        z3.ULT(id, dt.SCHED_NR_QUANTA),
        kernelstate.time[id].container ==
        util.global_field_element(ctx, '@time', 'container', 0, id))))

    conj.append(z3.ForAll([id], z3.Implies(
        z3.ULT(id, dt.SCHED_NR_QUANTA),
        kernelstate.time[id].thread ==
        util.global_field_element(ctx, '@time', 'thread', 0, id))))


def state_equiv(ctx, kernelstate):
    conj = []

    module = sys.modules[__name__]
    for k in kernelstate._meta.keys():
        if not k in kernelstate._structs:
            continue
        getattr(module, k + '_equiv')(conj, ctx, kernelstate)

    conj.append(kernelstate.root_container_id ==
        util.global_value(ctx, "@root_container_id"))

    conj.append(kernelstate.current_slot == util.global_value(ctx, "@current_ptr"))
    conj.append(kernelstate.current == ctx.globals['#current_thread'])
    conj.append(kernelstate.idle == util.global_value(ctx, '@idle'))

    p = util.FreshBitVec('p', 64)
    tlsidx = util.FreshBitVec('tlsidx', 64)

    conj.append(z3.ForAll([p, tlsidx],
                ctx.globals['#tls'](p, tlsidx) == kernelstate._tls(p, tlsidx)))

    conj.append(invariants.impl_invariants(ctx))
    conj.append(lemmas.ok(kernelstate))
    conj.append(lemmas.label_unique_ok(kernelstate))
    conj.append(lemmas.tls_unique_ok(kernelstate))

    return z3.And(*conj)
