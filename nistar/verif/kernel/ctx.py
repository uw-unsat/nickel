from __future__ import absolute_import
import z3

import libirpy
import libirpy.cstdlib as cstdlib
import libirpy.datatypes as idt
import libirpy.util as util

import nistar.impl as impl

import datatypes as dt
import state
from spec import label as l


def kpage_to_upage(ctx, kptr, uptr):
    id = kptr.getelementptr(dt.i64(0), dt.i64(0), dt.i64(0)).read(ctx)
    gen = kptr.getelementptr(dt.i64(0), dt.i64(0), dt.i64(1)).read(ctx)
    upage = z3.Concat(gen, id)
    uptr.getelementptr(dt.i64(0), dt.i64(0)).write(ctx, upage)


def upage_to_kpage(ctx, uptr, kptr):
    upage = uptr.getelementptr(dt.i64(0), dt.i64(0)).read(ctx)
    gen = z3.Extract(127, 64, upage)
    id = z3.Extract(63, 0, upage)
    kptr.getelementptr(dt.i64(0), dt.i64(0), dt.i64(0)).write(ctx, id)
    kptr.getelementptr(dt.i64(0), dt.i64(0), dt.i64(1)).write(ctx, gen)


def _copy_from_user(ctx, top, frm, n):
    n = n.as_long()
    assert n < dt.TLS_NR_SLOTS
    assert util.path_condition_implies(ctx, z3.ULE(frm, dt.TLS_NR_SLOTS - n))

    if isinstance(top, idt.BitcastPointer):
        assert not top._geps
        top = top._ptr

    assert top.type().is_pointer()

    current = get_current_thread(ctx)

    if top.type().deref(True).is_int():
        for i in range(n):
            val = ctx.globals['#tls'](current, frm + i)
            assert val.size() == 64
            top.getelementptr(util.i64(0), util.i64(i)).write(ctx, val)
    elif top.type().deref(True)._name == 'struct.usymlink_t':
        page = z3.Concat(ctx.globals['#tls'](current, frm + 1), ctx.globals['#tls'](current, frm + 0))
        parent = z3.Concat(ctx.globals['#tls'](current, frm + 3), ctx.globals['#tls'](current, frm + 2))
        top.getelementptr(util.i64(0), util.i64(0), util.i64(0)).write(ctx, page)
        top.getelementptr(util.i64(0), util.i64(0), util.i64(1)).write(ctx, parent)
    elif top.type().deref(True).is_struct():
        for i in range(n):
            val = ctx.globals['#tls'](current, frm + i)
            assert val.size() == 64
            top.getelementptr(util.i64(0), util.i64(0), util.i64(i)).write(ctx, val)

    return 0


def _copy_to_user(ctx, to, frmp, n):
    n = n.as_long()
    assert n < dt.TLS_NR_SLOTS
    assert util.path_condition_implies(ctx, z3.ULE(to, dt.TLS_NR_SLOTS - n))

    if isinstance(frmp, idt.BitcastPointer):
        assert not frmp._geps
        frmp = frmp._ptr

    assert frmp.type().is_pointer()

    current = get_current_thread(ctx)

    usize = frmp.type().deref().size()
    assert usize % 64 == 0
    if frmp.type().deref().is_array():
        assert n  == usize / 64
        src_start = frmp.getelementptr(ctx, dt.i64(0))
        # src_end = frmp.getelementptr(ctx, dt.i64(n - 1))

        start_path = src_start.canonical_path()
        # end_path = src_end.canonical_path()

        src_tup, start_args = frmp._ref.build_field_tuple_and_path(ctx, start_path)
        # _, end_args = frmp._ref.build_field_tuple_and_path(ctx, end_path)

        srcfn = ctx.references[frmp._ref._name][src_tup]
        dstfn = ctx.globals['#tls']

        def newf(*args):
            cond = []

            assert len(args) == 2

            cond.append(args[0] == current)
            cond.append(z3.UGE(args[1], to))
            cond.append(z3.ULT(args[1], to + n))

            cond = z3.And(*cond)

            srcargs = start_args[:-1] + [args[-1] - to]

            return util.If(cond, srcfn(*srcargs), dstfn(*args))

        ctx.globals['#tls'] = newf
        return

    elif frmp.type().deref().is_struct() and frmp.type().deref()._name == 'struct.usymlink_t':
        page = frmp.getelementptr(ctx, util.i64(0), util.i64(0)).read(ctx)
        parent = frmp.getelementptr(ctx, util.i64(0), util.i64(1)).read(ctx)

        ctx.globals['#tls'] = util.partial_update(ctx.globals['#tls'],
                                                 (current, to + 0,), z3.Extract(63, 0, page))
        ctx.globals['#tls'] = util.partial_update(ctx.globals['#tls'],
                                                 (current, to + 1,), z3.Extract(127, 64, page))

        ctx.globals['#tls'] = util.partial_update(ctx.globals['#tls'],
                                                 (current, to + 2,), z3.Extract(63, 0, parent))
        ctx.globals['#tls'] = util.partial_update(ctx.globals['#tls'],
                                                 (current, to + 3,), z3.Extract(127, 64, parent))

    elif usize / 64 == n:
        val = frmp.getelementptr(dt.i64(0), dt.i64(0)).read(ctx)
        for i in range(usize / 64):
            if val.size() > 64:
                v = z3.simplify(z3.Extract(64 * (i + 1) - 1, 64 * i, val))
            else:
                v = frmp.getelementptr(dt.i64(0), dt.i64(i)).read(ctx)
            ctx.globals['#tls'] = util.partial_update(ctx.globals['#tls'], (current, to + i,), v)
    else:
        assert usize == 64
        for i in range(n):
            v = frmp.getelementptr(dt.i64(0), dt.i64(i)).read(ctx)
            ctx.globals['#tls'] = util.partial_update(ctx.globals['#tls'], (current, to + i,), v)
    return 0


def get_current_thread(ctx):
    return ctx.globals['#current_thread']


def labelp_has(ctx, a, t1, t2):
    return ctx.globals['#label'].has(a, z3.Concat(t2, t1))


def labelp_is_subsetx(ctx, a, b, x):
    return ctx.globals['#label'].is_subsetx(a, b, x)


def labelp_is_subset(ctx, a, b):
    return ctx.globals['#label'].is_subset(a, b)


def label_is_subset(ctx, a, b):
    return l.is_subset(a.has, b.has)


def label_is_subsetx(ctx, a, b, x):
    return l.is_subsetx(a.has, b.has, x.has)


def make_label(ctx, bufp):
    start = bufp.getelementptr(ctx, dt.i64(0)).canonical_path()
    _tup, _args = bufp._ref.build_field_tuple_and_path(ctx, start)
    buffn = ctx.references[bufp._ref._name][_tup]

    def buf(idx):
        args = _args[:]
        args[-1] = idx
        return buffn(*args)

    def loop_inv(slot, has, idx, tags, data):
        i = util.FreshBitVec('i', 64)
        tag = util.FreshBitVec('tag', dt.tag_t)
        conj = []

        conj.append(z3.ULE(slot, dt.i64(dt.LABEL_NR_TAGS)))

        conj.append(
            z3.ForAll([tag],
                z3.Implies(has(tag), z3.ULT(idx(tag), slot),
        )))

        conj.append(
            z3.ForAll([tag],
                z3.Implies(tag != dt.TAG_INVALID,
                    has(tag) == (tags(idx(tag)) == tag)
        )))

        conj.append(z3.Not(has(dt.TAG_INVALID)))

        conj.append(z3.ForAll([i], z3.Implies(z3.ULT(i, slot), z3.And(
            (tags(i) != dt.TAG_INVALID) == has(tags(i)),
            tags(i) == z3.Concat(data(i * 2 + 1), data(i * 2)),
            data(i * 2) == buf(i * 2),
            data(i * 2 + 1) == buf(i * 2 + 1),
        ))))

        return z3.And(*conj)

    slot = util.FreshBitVec('fresh.slot', 64)
    has = util.FreshFunction('fresh.label_has', dt.tag_t, dt.bool_t)
    idx = util.FreshFunction('fresh.idx', dt.tag_t, dt.uint64_t)
    tags = util.FreshFunction('fresh.tags', dt.uint64_t, dt.tag_t)
    data = util.FreshFunction('fresh.data', dt.uint64_t, dt.uint64_t)

    I = loop_inv(slot, has, idx, tags, data)
    cond = z3.ULT(slot, dt.LABEL_NR_TAGS)

    la = dt.Label(has, idx, tags, data)

    if not hasattr(ctx, '_assumptions'):
        ctx._assumptions = []
    ctx._assumptions.append(I)
    ctx._assumptions.append(z3.Not(cond))

    return la


def label_has(ctx, la, tag1, tag2):
    return la.has(z3.Concat(tag2, tag1))


def tag_encrypt(ctx, dst, src):
    dst.write(ctx, src.read(ctx))


def get_label(ctx, id):
    data = ctx.call('@page_data', id)._ptr
    return dt.Label(lambda t: ctx.globals['#label'].has(id, t), None, None, data, id=id)


def set_label(ctx, label, new):
    ctx.globals['#label'].label = lambda pn, tag, oldfn: util.If(pn == label, new.has(tag), oldfn(pn, tag))

    # memset label data
    pd = util.global_to_uf_dict(ctx, '@pages_data')[()]
    pd = lambda nop, pn, idx, oldfn=pd: util.If(pn == label, new.data(idx), oldfn(nop, pn, idx))
    util.global_to_uf_dict(ctx, '@pages_data')[()] = pd


def llvm_memset(ctx, ptr, val, size, *args):
    val = z3.simplify(z3.Concat(*([val] * 8)))
    assert val.size() == 64

    size = util.as_long(size)
    assert size % 8 == 0
    size = size / 8

    for i in range(size):
        ptr._ptr.getelementptr(util.i64(0), util.i64(i)).write(ctx, val)


def llvm_memcpy(ctx, dst, src, size, *args):
    size = util.as_long(size)
    assert not src._geps
    assert not dst._geps
    src = src._ptr
    dst = dst._ptr

    assert size % 8 == 0
    size = size / 8

    typ = src.type().deref(True)

    if typ.is_struct() and typ._name == 'struct.ksymlink_t':
        assert size == 4
        val = src.getelementptr(dt.i64(0), dt.i64(0), dt.i64(0), dt.i64(0)).read(ctx)
        dst.getelementptr(dt.i64(0), dt.i64(0)).write(ctx, val)

        val = src.getelementptr(dt.i64(0), dt.i64(0), dt.i64(0), dt.i64(1)).read(ctx)
        dst.getelementptr(dt.i64(0), dt.i64(1)).write(ctx, val)

        val = src.getelementptr(dt.i64(0), dt.i64(0), dt.i64(1), dt.i64(0)).read(ctx)
        dst.getelementptr(dt.i64(0), dt.i64(2)).write(ctx, val)

        val = src.getelementptr(dt.i64(0), dt.i64(0), dt.i64(1), dt.i64(1)).read(ctx)
        dst.getelementptr(dt.i64(0), dt.i64(3)).write(ctx, val)
    else:
        for i in range(size):
            val = src.getelementptr(dt.i64(0), dt.i64(i)).read(ctx)
            dst.getelementptr(dt.i64(0), dt.i64(i)).write(ctx, val)


def sched_run(ctx, id):
    ctx.globals['#current_thread'] = id
    return None


def thread_clear_tls(ctx, id):
    ctx.globals['#tls'] = util.partial_update(ctx.globals['#tls'], (id,), util.i64(0))


def newctx():
    ctx = libirpy.newctx(prune_depth=1000)
    # If we don't need the values of any constants we don't have to
    # initialize them, slightly faster execution time.
    ctx.eval.declare_global_constant = ctx.eval.declare_global_variable
    libirpy.initctx(ctx, impl)

    ctx.globals['#tls'] = util.FreshFunction("tls", dt.uint64_t, dt.uint64_t, dt.uint64_t)
    ctx.globals['#current_thread'] = util.FreshBitVec("current_thread", dt.uint64_t)
    ctx.globals['#label'] = state.ImplLabel()

    ctx.globals['@pdb'] = cstdlib.pdb
    # ctx.globals['@bzero'] = cstdlib.bzero
    ctx.globals['@memcpy'] = cstdlib.memcpy
    ctx.globals['@memset64'] = cstdlib.memset64
    ctx.globals['@memset'] = cstdlib.memset
    ctx.globals['@panic'] = cstdlib.panic
    ctx.globals['@ASSUME'] = cstdlib.assume

    ctx.globals['@tag_encrypt'] = tag_encrypt

    # ctx.globals['@make_label'] = make_label
    ctx.globals['@get_label'] = get_label
    ctx.globals['@set_label'] = set_label

    ctx.globals['@kpage_to_upage'] = kpage_to_upage
    ctx.globals['@upage_to_kpage'] = upage_to_kpage

    ctx.globals['@_copy_from_user'] = _copy_from_user
    ctx.globals['@_copy_to_user'] = _copy_to_user

    ctx.globals['@get_current_thread'] = get_current_thread
    ctx.globals['@thread_init_fpstate'] = cstdlib.nop

    ctx.globals['@labelp_has'] = labelp_has
    ctx.globals['@labelp_is_subsetx'] = labelp_is_subsetx
    ctx.globals['@labelp_is_subset'] = labelp_is_subset

    ctx.globals['@label_is_subset'] = label_is_subset
    ctx.globals['@label_is_subsetx'] = label_is_subsetx
    ctx.globals['@label_has'] = label_has

    ctx.globals['@llvm_lifetime_start_p0i8'] = cstdlib.nop
    ctx.globals['@llvm_lifetime_end_p0i8'] = cstdlib.nop
    ctx.globals['@llvm_memset_p0i8_i64'] = llvm_memset
    ctx.globals['@llvm_memcpy_p0i8_p0i8_i64'] = llvm_memcpy
    ctx.globals['@llvm_assume'] = cstdlib.nop

    ctx.globals['@cpu_invalidate_pgtable'] = cstdlib.nop
    ctx.globals['@sched_run'] = sched_run
    ctx.globals['@thread_clear_tls'] = thread_clear_tls

    return ctx


