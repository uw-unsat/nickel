import z3

import libirpy.util as util

import datatypes as dt


def is_tag_valid(tag):
    return tag != dt.MAX_VAL(tag)


def equiv(spec, ctx, la):
    tag = util.FreshBitVec('tag', dt.tag_t)
    return z3.ForAll([tag], z3.Implies(
        is_tag_valid(tag),
        label_has(spec, tag) ==
        ctx.call("@label_has", la, z3.Extract(127, 64, tag), z3.Extract(63, 0, tag))))


def label_has(la, tag):
        return la.label(tag)


def label_add(la, tag):
        newla = la.copy()
        newla.label[tag] = z3.BoolVal(True)
        return newla

def is_empty(a):
    tag = util.FreshBitVec('tag', dt.tag_t)
    return z3.ForAll([tag], z3.Not(a(tag)))


def is_subset(a, b):
    tag = util.FreshBitVec('tag', dt.tag_t)
    return z3.ForAll([tag], z3.Implies(a(tag), b(tag)))


def is_subsetx(a, b, x):
    tag = util.FreshBitVec('tag', dt.tag_t)
    return z3.ForAll([tag], z3.Implies(a(tag),
                                       z3.Or(b(tag), x(tag))))


def union(a, b):
    return lambda tag: z3.Or(a(tag), b(tag))


def can_read(a, b, x):
    return z3.And(
            is_subsetx(b[0], a[0], x),
            is_subsetx(a[1], b[1], x))


def can_write(a, b, x):
    return z3.And(
            is_subsetx(a[0], b[0], x),
            is_subsetx(b[1], a[1], x))


def can_read_write(a, b, x):
    return z3.And(
            can_read(a, b, x),
            can_write(a, b, x))


def universal():
    return lambda t: z3.BoolVal(True)


def empty():
    return lambda t: z3.BoolVal(False)


def flow(a, b, x=empty()):
    return z3.And(
            is_subsetx(a.secrecy, b.secrecy, x),
            is_subsetx(b.integrity, a.integrity, x))


def flowW(a, b):
    return flow(a, b, a.ownership)


def flowR(a, b):
    return flow(a, b, b.ownership)


def interference(a, b):
    return flow(a, b, union(a.ownership, b.ownership))


def equal(a, b):
    t = util.FreshBitVec('tag', dt.tag_t)
    return z3.ForAll([t], z3.Implies(
            a.secrecy(t) == b.secrecy(t),
            a.integrity(t) == b.integrity(t),
            a.ownership(t) == b.ownership(t)))

