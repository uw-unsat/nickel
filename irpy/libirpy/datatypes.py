import z3
import copy
import types

from . import util


class Reference(object):
    def __init__(self, name, itype):
        self._type = itype
        self._name = name
        self._length = None
        self._arity = None

    def __eq__(self, other):
        return self._type == other._type and self._name == other._name

    def arity(self, ctx, path):
        if self._arity:
            return self._arity
        fields_tup, path = self.build_field_tuple_and_path(ctx, path)
        refs = ctx.references[self._name]
        arities = set()
        if fields_tup not in refs:
            for k, v in list(refs.items()):
                arities.add(v.arity())
            assert len(arities) == 1
            self._arity = list(arities)[0]
        else:
            if hasattr(refs[fields_tup], 'arity') and callable(refs[fields_tup].arity):
                self._arity = refs[fields_tup].arity()
            else:
                # Just try to guess..
                args = []
                while True:
                    try:
                        refs[fields_tup](*args)
                        break
                    except:
                        if len(args) > 10:
                            raise RuntimeError("Could not figure out arity")
                        args.append(util.i64(0))
                self._arity = len(args)

        return self._arity

    def build_field_tuple_and_path(self, ctx, path):
        typ = self._type
        fields = []
        newpath = []
        while len(path) > 0:
            if typ.is_int():
                raise Exception("Can't have base type if there is more left in path")
            elif typ.is_array() or typ.is_pointer():
                if typ.is_array():
                    if not util.path_condition_implies(ctx, z3.ULT(path[0],
                        typ.length()), print_model=True):
                        util.print_stacktrace(ctx)
                        raise IndexError(
                            "Can not prove index %s is within array bounds %s"
                            % (path[0], typ.length()))

                if typ.is_pointer():
                    if not util.path_condition_implies(ctx, path[0] == 0):
                        util.print_stacktrace(ctx)
                        raise RuntimeError("Pointer arithmetic not supported")

                typ = typ.deref()
                newpath.append(path[0])
            elif typ.is_struct():
                field = util.as_long(path[0])
                fields.append(field)
                typ = typ.field(field)
            elif typ.is_union:
                if not util.as_long(path[0]) == 0:
                    raise IndexError("Union not supported")
                field = util.as_long(path[0])
                fields.append(field)
                typ = typ.field(field)
            else:
                raise Exception("Unhandled case")
            path = path[1:]
        return tuple(fields), newpath

    def read(self, ctx, path):
        fields_tup, path = self.build_field_tuple_and_path(ctx, path)
        ctx.accessed.add(self._name)
        return ctx.references[self._name][fields_tup](*path)

    def write(self, ctx, path, value):
        fields_tup, path = self.build_field_tuple_and_path(ctx, path)
        oldf = ctx.references[self._name][fields_tup]
        newf = util.partial_update(oldf, path, value)
        ctx.accessed.add(self._name)
        ctx.references[self._name][fields_tup] = newf


class BitcastPointer(object):
    def __init__(self, ptr, type, geps=None, origin=None):
        assert isinstance(ptr, Pointer)
        self._ptr = ptr
        self._type = type
        if geps is None:
            geps = []
        self._geps = geps
        self._origin = origin

    def __repr__(self):
        return "BitcastPointer<{!r} - {!r}>".format(self._ptr, self._type)

    def __eq__(self, other):
        return (self._type == other._type and self._ptr == other._ptr
                and self._geps == other._geps)

    def type(self):
        return self._type

    def getelementptr(self, ctx, *idxs, **kwargs):
        type = kwargs.pop('type', self._type)
        assert type == self._type
        assert kwargs == {}, "Unexpected argument {}".format(kwargs)
        assert len(idxs) > 0, "Can not have empty gep"
        geps = self._geps[:]
        geps.append((idxs, self._type))
        return BitcastPointer(self._ptr, type, geps=geps)

    def canonical_path(self):
        if not self._geps:
            return self._ptr.canonical_path()
        else:
            raise NotImplementedError("Can not canonicalize gep'd bitcast ptr")

    def canonical_ptr(self, ctx):
        # support for very simple bitcast geps.
        # only if the gep is a multiple of the underlaying pointer read
        # size do we allow it.
        inner = self._ptr.read(ctx)
        isize = inner.size()

        assert len(self._geps) == 1
        assert len(self._geps[0]) == 2
        assert len(self._geps[0][0]) == 1
        gepsize = self._geps[0][1].deref().size()
        gep = self._geps[0][0][0]

        gep = util.as_long(gep)

        assert (gep * gepsize) % isize == 0

        p = self._ptr.getelementptr(ctx, util.i64(gep * gepsize / isize))
        return BitcastPointer(p, self.type())

    def bitcast(self, ctx, typ):
        return BitcastPointer(self._ptr, typ, geps=self._geps[::])

    def read(self, ctx):
        if not self._geps:
            bsize = self._type.deref().size()
            val = self._ptr.read(ctx)
            return z3.Extract(bsize - 1, 0, val)
        else:
            return self.canonical_ptr(ctx).read(ctx)

    def write(self, ctx, value):
        if not self._geps:
            assert self._type.is_pointer()
            bsize = self._type.deref().size()
            val = self._ptr.read(ctx);
            assert val.size() >= bsize
            if val.size() - bsize == 0:
                return self._ptr.write(ctx, value)
            else:
                self._ptr.write(ctx,
                    z3.Concat(z3.Extract(val.size() - 1, bsize, val), value))
        else:
            return self.canonical_ptr(ctx).write(ctx, value)


class Pointer(object):
    def __init__(self, ref, geps=None, type=None):
        assert ref is None or isinstance(
            ref, Reference), "Pointer must point to a reference or None"
        if geps is None:
            geps = []
        self._geps = geps
        self._ref = ref
        self._type = type

    def __repr__(self):
        return "Pointer<{!r} - {!r}>".format(self._ref, self._type)

    def __eq__(self, other):
        return (self._geps == other._geps and self._ref == other._ref
                and self.type() == other.type())

    def type(self):
        return self._type

    def ite(self, other, cond):
        p1 = copy.deepcopy(self)
        p2 = copy.deepcopy(other)
        assert p1.type() == p2.type()

        def inner_write(self, ctx, value):
            p1.write(ctx, util.If(cond, value, p1.read(ctx)))
            p2.write(ctx, util.If(z3.Not(cond), value, p2.read(ctx)))

        def inner_read(self, ctx):
            return util.If(cond, p1.read(ctx), p2.read(ctx))

        def inner_getelementptr(self, ctx):
            raise Exception("GEP on ite pointer")

        p = Pointer(None, type=p1.type())

        p.write = types.MethodType(inner_write, p)
        p.read = types.MethodType(inner_read, p)
        p.getelementptr = types.MethodType(inner_getelementptr, p)

        return p

    def bitcast(self, ctx, typ):
        p = self
        arity = p._ref.arity(ctx, self.canonical_path())
        assert arity >= len(p._geps)
        while arity > len(p.canonical_path()):
            p = p.getelementptr(ctx, z3.BitVecVal(0, 64), z3.BitVecVal(0, 64), type=self._type)
        return BitcastPointer(p, typ, origin=self)

    # Just apppend the gep
    def getelementptr(self, ctx, *idxs, **kwargs):
        type = kwargs.pop('type', self._type)
        assert kwargs == {}, "Unexpected argument {}".format(kwargs)
        assert len(idxs) > 0, "Cannot have empty gep"
        geps = self._geps[:]
        geps.append(idxs)
        return Pointer(self._ref, geps, type=type)

    def canonical_path(self):
        path = [util.i64(0)]
        for gep in self._geps:
            assert len(gep) > 0, "Cannot have empty gep"
            if hasattr(gep[0], 'sexpr') and gep[0].size() != 64:
                path[-1] = path[-1] + z3.BitVecVal(util.as_long(gep[0]), 64)
            else:
                path[-1] = path[-1] + gep[0]
            path += gep[1:]
        return list(map(util.simplify, path))

    def read(self, ctx):
        return self._ref.read(ctx, self.canonical_path())

    def write(self, ctx, value):
        return self._ref.write(ctx, self.canonical_path(), value)


def init_ref(ctx, ref):
    d = {}
    l = {}
    def _fresh_ref(typ, tup, length, depth, name=None):
        if typ.is_pointer() and depth != 0:
            d[tup] = None
            l[tup] = length
        if typ.is_int() or (typ.is_pointer() and depth != 0):
            args = [z3.BitVecSort(64)] * depth + [z3.BitVecSort(typ.size())]
            if name is None:
                name = ref._name
            else:
                name = ref._name + "->" + name
            d[tup] = z3.Function(util.fresh_name(name), *args)
            l[tup] = length
        elif typ.is_struct():
            for i in range(len(typ.fields())):
                _fresh_ref(typ.field(i), tup + (i,), length + (1,), depth, typ.field_name(i))
        elif typ.is_array() or typ.is_pointer() or typ.is_vector():
            ll = getattr(typ, 'length', lambda *args: 1)()
            _fresh_ref(typ.deref(), tup, length + (ll,), depth + 1)
        elif typ.is_union() and len(typ.fields()) == 1:
            # We can strip the union away if there's only one field
            if len(typ.fields()) == 1:
                _fresh_ref(typ.field(0), tup + (0,), length + (1,), depth, name)
        elif type.is_union():
            # FIXME unions
            raise NotImplementedError('fresh_ref not implemented for union: {!r}'.format(typ))
        else:
            raise Exception("Unhandled fresh_ref case: {!r}").format(typ)

    _fresh_ref(ref._type, (), (), 0)
    assert ref._name not in ctx.references, "Overwriting a reference, this is probably a bug"
    ref._length = l
    ctx.references[ref._name] = d


def fresh_ptr(ctx, name, type):
    ref = Reference(name, type)
    init_ref(ctx, ref)
    return Pointer(ref, type=type)
