# -*- encoding: UTF-8
import z3

import libirpy.util as util

import datatypes as dt
import label as l


def current_eq(s1, s2):
    conj = []

    idx = util.FreshBitVec('tlsidx', dt.size_t)
    conj.append(s1.current == s2.current)
    conj.append(z3.ForAll([idx], z3.Implies(
        z3.ULT(idx, dt.TLS_NR_SLOTS),
        s1.tls(idx) == s2.tls(idx))))
    conj.append(obj_equiv(s1, s2, s1.current))

    return z3.And(*conj)


def state_equiv(conj, s1, s2):
    conj.append(s1.root_container_id == s2.root_container_id)
    conj.append(s1.pages[s1.root_container_id].generation == s2.pages[s2.root_container_id].generation)
    conj.append(s1.current_slot == s2.current_slot)
    conj.append(s1.idle == s2.idle)


def standard_obj_equiv(conj, s1, s2, id):
    idx = util.FreshBitVec('idx', dt.uint64_t)

    # Most page metadata fields
    conj.append(s1.pages[id].generation == s2.pages[id].generation)
    conj.append(s1.pages[id].type == s2.pages[id].type)
    conj.append(s1.pages[id].secrecy == s2.pages[id].secrecy)
    conj.append(s1.pages[id].integrity == s2.pages[id].integrity)
    conj.append(s1.pages[id].parent == s2.pages[id].parent)
    conj.append(s1.pages[id].parent_slot == s2.pages[id].parent_slot)
    conj.append(s1.pages[id].tag_counter == s2.pages[id].tag_counter)

    # name and metadata
    conj.append(z3.ForAll([idx], z3.Implies(
        z3.ULT(idx, dt.PAGE_NAME_LEN),
        s1.pages[id].name(idx) == s2.pages[id].name(idx))))

    conj.append(z3.ForAll([idx], z3.Implies(
        z3.ULT(idx, dt.PAGE_METADATA_LEN),
        s1.pages[id].metadata(idx) == s2.pages[id].metadata(idx))))

    # Data fields
    conj.append(z3.ForAll([idx],
        z3.Implies(z3.ULT(idx, dt.KPAGE_SIZE),
            s1.pages[id].data(idx) == s2.pages[id].data(idx))))


def label_equiv(s1, s2, id, conj=None):
    if conj is None:
        conj = []

    tag = util.FreshBitVec('tag', dt.tag_t)

    standard_obj_equiv(conj, s1, s2, id)

    # Label equivalence
    conj.append(z3.ForAll([tag], z3.Implies(
        s1.pages[id].type == dt.PAGE_TYPE_LABEL,
        s1.pages.label[id].label(tag) == s2.pages.label[id].label(tag))))

    return z3.And(*conj)


def obj_equiv(s1, s2, id):
    idx = util.FreshBitVec('idx', dt.uint64_t)

    conj = []

    standard_obj_equiv(conj, s1, s2, id)
    label_equiv(s1, s2, s1.pages[id].secrecy, conj=conj)
    label_equiv(s1, s2, s1.pages[id].integrity, conj=conj)

    # parent's generation is the same
    conj.append(s1.pages[s1.pages[id].parent].generation ==
                s2.pages[s2.pages[id].parent].generation)

    # Container equivalence. Some metadata for pages within a container are
    # covered by the container's labels (like type and generation)
    conj.append(z3.Implies(s1.pages[id].type == dt.PAGE_TYPE_CONTAINER,
        z3.And(
            s1.pages[id].quota == s2.pages[id].quota,
            s1.pages[id].uquota == s2.pages[id].uquota,
            s1.pages[id].qquota == s2.pages[id].qquota,

            z3.ForAll([idx], z3.Implies(
                z3.And(
                    z3.ULT(idx, dt.SCHED_NR_QUANTA),
                    z3.Or(
                        s1.time[idx].container == id,
                        s2.time[idx].container == id)),
                z3.And(
                    s1.time[idx].thread == s2.time[idx].thread,
                    s1.time[idx].container == s2.time[idx].container))),

            z3.ForAll([idx], z3.Implies(
                z3.ULT(idx, s1.pages[id].quota),
                z3.And(
                    # The freelist contains the same free pages
                    s1.pages[id].list(idx) == s2.pages[id].list(idx),
                    # And their generations are the same.
                    s1.pages[s1.pages[id].list(idx)].generation ==
                    s2.pages[s2.pages[id].list(idx)].generation,

                    # Tag counters are the same
                    s1.pages[s1.pages[id].list(idx)].tag_counter ==
                    s2.pages[s2.pages[id].list(idx)].tag_counter,
                    ))),

            z3.ForAll([idx], z3.Implies(
                z3.ULT(idx, s1.pages[id].uquota),
                # The ufreelist contains the same free pages
                s1.pages[id].ulist(idx) == s2.pages[id].ulist(idx))),

            z3.ForAll([idx], z3.Implies(
                z3.And(
                    z3.ULT(idx, dt.KPAGE_SIZE),
                    dt.page_is_valid((s1.pages[id].data(idx)))),
                z3.And(
                    s1.pages[s1.pages[id].data(idx)].type == s2.pages[s2.pages[id].data(idx)].type,
                    s1.pages[s1.pages[id].data(idx)].generation == s2.pages[s2.pages[id].data(idx)].generation,
                    s1.pages[s1.pages[id].data(idx)].secrecy == s2.pages[s2.pages[id].data(idx)].secrecy,
                    s1.pages[s1.pages[id].data(idx)].integrity == s2.pages[s2.pages[id].data(idx)].integrity,
                    z3.Implies(s1.pages[s1.pages[id].data(idx)].type  == dt.PAGE_TYPE_UNTYPED,
                        s1.pages[s1.pages[id].data(idx)].tag_counter == s2.pages[s2.pages[id].data(idx)].tag_counter),
                    z3.Implies(
                        z3.And(
                            s1.pages[s1.pages[id].data(idx)].type != dt.PAGE_TYPE_UNTYPED,
                            s1.pages[s1.pages[id].data(idx)].type != dt.PAGE_TYPE_THREAD,
                        ),
                        z3.And(
                            label_equiv(s1, s2,
                                s1.pages[s1.pages[id].data(idx)].secrecy),
                            label_equiv(s1, s2,
                                s1.pages[s1.pages[id].data(idx)].integrity))),

                    z3.Implies(
                        s1.pages[s1.pages[id].data(idx)].type == dt.PAGE_TYPE_GATE,
                        z3.And(
                            s1.pages.ownership(s1.pages[id].data(idx)) ==
                            s2.pages.ownership(s1.pages[id].data(idx)),
                            label_equiv(s1, s2,
                                s1.pages.ownership(s1.pages[id].data(idx))))),


                ))))))

    # Block equivalence
    conj.append(z3.Implies(s1.pages[id].type == dt.PAGE_TYPE_BLOCK,
        z3.And(
            z3.ForAll([idx], z3.Implies(
                z3.ULT(idx, dt.PAGE2M_SIZE),
                s1.upages[s1.pages[id].data(0)].data(idx) ==
                s2.upages[s2.pages[id].data(0)].data(idx))))))

    # Gate equivalence
    conj.append(z3.Implies(s1.pages[id].type == dt.PAGE_TYPE_GATE,
        z3.And(
            label_equiv(s1, s2, s1.pages.ownership(id)),
            label_equiv(s1, s2, s1.pages.gate_guard(id)))))

    idx = util.FreshBitVec('tlsidx', dt.size_t)

    # Thread equivalence
    conj.append(z3.Implies(
        s1.pages[id].type == dt.PAGE_TYPE_THREAD,
        z3.And(
            label_equiv(s1, s2, s1.pages.ownership(id)),
            # TLS
            z3.ForAll([idx],z3.Implies(
                z3.ULT(idx, dt.TLS_NR_SLOTS),
                s1._tls(id, idx) == s2._tls(id, idx)))
            )))

    return z3.And(*conj)


def obj_label(s, id):
    """Returns the label (domain) of an object"""

    secrecy = s.pages.label[s.pages[id].secrecy].label
    integrity = s.pages.label[s.pages[id].integrity].label
    ownership = lambda t: s.pages.label[s.pages.ownership(id)].label(t)

    o = util.If(z3.Or(
        s.pages[id].type == dt.PAGE_TYPE_THREAD,
        s.pages[id].type == dt.PAGE_TYPE_GATE),
        ownership, l.empty())

    return dt.Domain(secrecy, integrity, o)


def can_read_obj(s, id, L):
    return z3.And(dt.page_is_valid(id),
                  z3.UGT(s.pages[id].type, dt.PAGE_TYPE_LABEL),
                  l.flowR(obj_label(s, id), L))


def can_write_obj(s, id, L):
    return z3.And(dt.page_is_valid(id),
                  z3.UGT(s.pages[id].type, dt.PAGE_TYPE_LABEL),
                  l.flowW(obj_label(s, id), L))


def obs_equivalence(s1, s2, L):
    """Observational equivalence with respect to a domain u.
    Each domain L is a triple <S, I, O>"""

    id = util.FreshBitVec('obj_eq', dt.page_id_t)
    conj = []

    state_equiv(conj, s1, s2)

    conj.append(z3.ForAll([id], z3.Implies(
       # s1[id] ⊑r L \/ s2[id] ⊑r L
       z3.Or(
           can_read_obj(s1, id, L),
           can_read_obj(s2, id, L),
       ),
        # => s1[id] = s2[id]
        obj_equiv(s1, s2, id))))

    return z3.And(*conj)
