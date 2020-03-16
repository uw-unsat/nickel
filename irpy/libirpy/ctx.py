import copy
import z3
import warnings

from . import util
from . import z3eval
from . import itypes
from .solver import Solver


_solver = Solver()
_path_condition = []
_snapshots = []


class Context(object):
    def __init__(self, **kwargs):
        fields = [
            ('globals', {}),
            ('locals', []),
            ('stacktrace', []),
            ('metadata', {}),
            ('references', {}),
            ('ptr_to_int', {}),
            ('types', {}),
            ('typedefs', []),
            ('enums', []),
            ('side_conditions', {}),
            ('eval', None),
            ('depth', 0),
            ('prune_depth', 0),
            ('accessed', set()),
            ('assumptions', []),
        ]

        for (name, default) in fields:
            setattr(self, name, kwargs.get(name, default))

    def __repr__(self):
        return repr(self.__dict__)

    def add_assumption(self, assumption, pc_only=True):
        if pc_only:
            self.solver.add(assumption)
            self.path_condition.append(assumption)
        else:
            self.assumptions.append(assumption)

    def populate_globals(self, module):
        for k in dir(module):
            if k.startswith('func_'):
                gkey = '@' + k[len('func_'):]
                self.globals[gkey] = getattr(module, k)

    def populate_typedefs(self):
        for ident, metadata in list(self.metadata.items()):
            if isinstance(metadata, tuple):
                (type_, dict_) = metadata
                if type_ == 'DIDerivedType' and dict_['tag'] == 'DW_TAG_typedef':
                    name = dict_['name']
                    baseTypeId = dict_['baseType']
                    baseType = self._parse_typedef(baseTypeId)
                    if baseType is not None:
                        if name in self.types and baseType != self.types[name]:
                            from ipdb import set_trace; set_trace()
                            assert self.types[name] is None, "Trying to redeclare type {!r}".format(name)
                        self.types[name] = baseType
                        self.typedefs.append(name)

    def _parse_typedef(self, metakey):
        assert metakey in self.metadata, "typedef definition not found in metadata"
        (type_, dict_) = self.metadata[metakey]
        if type_ == 'DIDerivedType':
            return self._parse_typedef(dict_['baseType'])
        elif type_ == 'DIBasicType':
            assert 'size' in dict_
            return itypes.IntType(dict_['size'])
        elif type_ == 'DICompositeType':
            # warnings.warn("Skipping non-primitive typedef {!r}".format(metakey), DeprecationWarning)
            return None
        else:
            raise Exception("Unrecognized typedef definition: {!r}".format(metakey))

    def populate_enums(self):
        for k, v in list(self.metadata.items()):
            if isinstance(v, tuple) and v[0] == 'DICompositeType':
                if v[1].get('tag') == 'DW_TAG_enumeration_type':
                    name = v[1].get('name')
                    size = v[1].get('size')
                    elements = v[1].get('elements')

                    if name is None or size is None or elements is None:
                        continue

                    type_ = itypes.IntType(size)

                    values = {}
                    for element in self.metadata.get(elements):
                        element = self.metadata.get(element)
                        assert element[0] == 'DIEnumerator'
                        element_name = element[1].get('name')
                        element_value = element[1].get('value')
                        values[element_name] = element_value

                    self.enums.append((name, type_, values))

    @property
    def stack(self):
        return self.locals[-1]

    @property
    def solver(self):
        return _solver

    @solver.setter
    def solver(self, s):
        global _solver
        _solver = s

    @property
    def path_condition(self):
        return _path_condition

    @property
    def _snapshots(self):
        return _snapshots

    def snapshot(self):
        return copy.deepcopy(self)

    def restore(self, c):
        self.globals = c.globals
        self.locals = c.locals
        self.references = c.references
        self.accessed = c.accessed

    def push(self, path_condition=z3.BoolVal(True)):
        c = self.snapshot()
        self._snapshots.append(c)

        self.solver.push()
        self.solver.add(path_condition)
        self.path_condition.append(path_condition)
        self.depth += 1

    def pop(self):
        self.depth -= 1
        self.path_condition.pop()
        self.solver.pop()

        ret = self.snapshot()

        c = self._snapshots.pop()
        self.restore(c)

        return ret

    def merge(self, cond, c1, c2):
        self.globals = util.merge(cond, c1.globals, c2.globals)
        self.locals = util.merge(cond, c1.locals, c2.locals)
        self.references = util.merge(cond, c1.references, c2.references)
        self.accessed = c1.accessed.union(c2.accessed)

        assert self.path_condition == c1.path_condition
        assert self.path_condition == c2.path_condition

        assert self.side_conditions == c1.side_conditions
        assert self.side_conditions == c2.side_conditions

    def call(self, fn, *args):
        try:
            self.locals.append({})
            self.stacktrace.append({})
            return self.globals[fn](self, *args)
        finally:
            self.stacktrace.pop()
            self.locals.pop()


def newctx(cls=Context, **kwargs):
    solver = Solver()
    solver.set(AUTO_CONFIG=False)

    ctx = cls(
        globals={},
        solver=solver,
        eval=z3eval.Z3IRPyEval(),
        prune_depth=kwargs.pop('prune_depth', 5),
        accessed=set(),
    )

    assert not kwargs, "Not all arguments were used."
    return ctx


def initctx(ctx, module):
    module._init_metadata(ctx)
    module._init_types(ctx)
    itypes.parse_struct_declarations(ctx)
    module._init_globals(ctx)
    ctx.populate_globals(module)
    ctx.populate_typedefs()
    ctx.populate_enums()
