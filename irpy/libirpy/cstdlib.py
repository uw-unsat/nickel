import copy
import z3

from libirpy.datatypes import BitcastPointer
import libirpy.ex as ex
import libirpy.itypes as itypes
import libirpy.util as util

from . import datatypes as dt
from .typedefs import i64


def pdb(ctx, *args, **kwargs):
    from ipdb import set_trace; set_trace()


def nop(ctx, *args, **kwargs):
    pass


def assume(ctx, cond):
    ctx.add_assumption(z3.Implies(z3.And(*ctx.path_condition), cond), pc_only=False)


def panic(ctx, *args, **kwargs):
    ue = ex.UnreachableException(ctx.path_condition[-1])
    ue.stacktrace = copy.deepcopy(ctx.stacktrace[-1])
    raise ue


def memcpy(ctx, dst, src, size):
    if isinstance(dst, dt.BitcastPointer):
        dst = dst._ptr
        dst_start = dst.getelementptr(ctx, i64(0))
        dst_end = dst.getelementptr(ctx, i64(0))
    else:
        dst_start = dst.getelementptr(ctx, i64(0), i64(0))
        dst_end = dst.getelementptr(ctx, i64(0), i64(0))

    if isinstance(src, dt.BitcastPointer):
        src = src._ptr
        src_start = src.getelementptr(ctx, i64(0))
        src_end = src.getelementptr(ctx, i64(0))
    else:
        src_start = src.getelementptr(ctx, i64(0), i64(0))
        src_end = src.getelementptr(ctx, i64(0), i64(0))


    # Same paranoid checks
    assert dst.type().is_pointer()
    assert src.type().is_pointer()

    assert dst.type().deref().is_array()
    assert src.type().deref().is_array()

    assert dst.type().deref().size() == src.type().deref().size()
    assert dst.type().deref().length() == src.type().deref().length()

    dst_start_path = dst_start.canonical_path()
    src_start_path = src_start.canonical_path()

    dst_end_path = dst_end.canonical_path()
    src_end_path = src_end.canonical_path()

    assert dst_start_path[-1].as_long() == src_start_path[-1].as_long()
    assert dst_end_path[-1].as_long() == src_end_path[-1].as_long()

    dst_tup, dst_start_args = dst._ref.build_field_tuple_and_path(
        ctx, dst_start_path)
    src_tup, src_start_args = src._ref.build_field_tuple_and_path(
        ctx, src_start_path)

    _, dst_end_args = dst._ref.build_field_tuple_and_path(ctx, dst_end_path)
    _, src_end_args = src._ref.build_field_tuple_and_path(ctx, src_end_path)

    dst_end_args[-1] += size
    src_end_args[-1] += size

    assert len(dst_start_args) == len(dst_end_args)
    assert len(dst_end_args) == len(src_end_args)

    dstfn = ctx.references[dst._ref._name][dst_tup]
    srcfn = ctx.references[src._ref._name][src_tup]

    # At this point we know that the src and dst are same-sized arrays.
    # They are both indexed starting from 0 up to length - 1.
    # So, we just do update the uf using an ite of the form
    # arg1 == dst_arg1, arg2 == dst_arg2, .. dst_argn_start <= arg1 < dst_argn_end

    def newf(*args):
        assert len(args) == len(dst_end_args)
        cond = []
        for a, b in zip(args[:-1], dst_start_args[:-1]):
            cond.append(a == b)

        cond.append(z3.UGE(args[-1], dst_start_args[-1]))
        cond.append(z3.ULT(args[-1], dst_end_args[-1]))

        cond = z3.And(*cond)

        srcargs = src_start_args[:-1] + [args[-1]]

        return util.If(cond, srcfn(*srcargs), dstfn(*args))

    ctx.references[dst._ref._name][dst_tup] = newf

    return dst


def memset64(ctx, ptr, val, size):
    assert ptr.type().deref().size() == 64
    for i in range(util.as_long(size)):
        ptr.getelementptr(util.i64(0), util.i64(i)).write(ctx, val)


def memset(ctx, ptr, val, size):
    val = z3.Extract(7, 0, val)

    size = size.as_long()

    # If we're passed a bitcasted pointer we just check if the write size is a
    # multiple of the underlying types write size, then we can just ignore the bitcast.
    if isinstance(ptr, BitcastPointer):
        # TODO: check for gep offset on the pointer.
        # If the bitcast pointer has been offset this is wrong.
        ptr = ptr._origin

    inner = ptr.type().deref()

    # We are memsetting an array whose inner type matches the size of the val
    assert inner.is_array()
    assert inner.deref().size() % val.size() == 0

    val = z3.Concat(*([val] * (inner.deref().size() // val.size())))

    if inner.deref().is_int():
        array_len = ptr.type().deref().length()

        dst_start = ptr.getelementptr(ctx, i64(0), i64(0))
        dst_end = ptr.getelementptr(
            ctx, i64(0), i64(array_len - 1))

        dst_start_path = dst_start.canonical_path()
        dst_end_path = dst_end.canonical_path()

        dst_tup, dst_start_args = ptr._ref.build_field_tuple_and_path(
            ctx, dst_start_path)
        _, dst_end_args = ptr._ref.build_field_tuple_and_path(
            ctx, dst_end_path)

        dstfn = ctx.references[ptr._ref._name][dst_tup]

        def newf(*args):
            assert len(args) == len(dst_end_args)
            cond = []
            for a, b in zip(args[:-1], dst_start_args[:-1]):
                cond.append(a == b)

            cond.append(z3.UGE(args[-1], dst_start_args[-1]))
            cond.append(z3.ULE(args[-1], dst_end_args[-1]))

            cond = z3.And(*cond)

            return util.If(cond, val, dstfn(*args))

        ctx.references[ptr._ref._name][dst_tup] = newf
        return ptr

    else:
        raise NotImplementedError(
            "Don't know how to memset {!r}".format(inner))


def bzero(ctx, ptr, size):
    size = size.as_long()

    # If we're passed a bitcasted pointer we just check if the write size is a
    # multiple of the underlying types write size, then we can just ignore the bitcast.
    if isinstance(ptr, BitcastPointer):
        ptr = ptr._ptr

    inner = ptr.type().deref()

    if inner.is_int():
        assert size * 8 <= 64
        ptr.write(ctx, z3.BitVecVal(0, size * 8))
    elif inner.is_struct():
        assert inner.size() / \
            8 == size, "Can not partially bzero a struct: {} v {}".format(
                inner.size() / 8, size)

        for i, field in enumerate(inner.fields()):
            subptr = ptr.getelementptr(ctx, i64(0), i64(i),
                                       type=itypes.PointerType(field))
            bzero(ctx, subptr, z3.simplify(z3.BitVecVal(field.size() / 8, 64)))
    elif inner.is_array():
        write_size = inner.deref().size()

        if inner.deref().is_int():

            array_len = ptr.type().deref().length()

            dst_start = ptr.getelementptr(ctx, i64(0), i64(0))
            dst_end = ptr.getelementptr(
                ctx, i64(0), i64(array_len - 1))

            dst_start_path = dst_start.canonical_path()
            dst_end_path = dst_end.canonical_path()

            dst_tup, dst_start_args = ptr._ref.build_field_tuple_and_path(
                ctx, dst_start_path)
            _, dst_end_args = ptr._ref.build_field_tuple_and_path(
                ctx, dst_end_path)

            dstfn = ctx['references'][ptr._ref._name][dst_tup]

            def newf(*args):
                assert len(args) == len(dst_end_args)
                cond = []
                for a, b in zip(args[:-1], dst_start_args[:-1]):
                    cond.append(a == b)

                cond.append(z3.UGE(args[-1], dst_start_args[-1]))
                cond.append(z3.ULE(args[-1], dst_end_args[-1]))

                cond = z3.And(*cond)

                return util.If(cond, z3.BitVecVal(0, write_size), dstfn(*args))

            ctx['references'][ptr._ref._name][dst_tup] = newf

        else:
            raise NotImplementedError(
                "Don't know how to bzero {!r}".format(inner))

    else:
        raise NotImplementedError("Don't know how to bzero {!r}".format(inner))
