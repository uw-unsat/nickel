
from libirpy import solver
from libirpy import util
from libirpy import ctx

import z3
import tempfile
import re
import unittest
import collections
import os
import sys
import inspect

tempdir = tempfile.mkdtemp()
print(f'SMT2 files located in {tempdir}')


Solver = None

try:
    import toml
    file = os.environ.get('SOLVER_CONF', 'solver.toml')
    if not os.path.isfile(file):
        file = '../solver.toml'
    conf = toml.load(os.environ.get('SOLVER_CONF', file))
    print(f'Solver configuration: \n\n{toml.dumps(conf)}')
    print(f'Using solver: {conf["solver"]["type"]}')
    if conf['solver']['type'] == 'local':
        Solver = z3.Solver
    elif conf['solver']['type'] == 'subprocess':
        Solver = solver.Solver
    elif conf['solver']['type'] == 'remote':
        class RemoteSolver(solver.Solver):
            def __init__(self):
                super().__init__(args=[
                    'ssh',
                    '-T',
                    conf['server']['host'],
                    conf['server']['python'],
                    conf['server']['server'],
                ])
        Solver = RemoteSolver
    else:
        Solver = solver.Solver
except:
    print("Failed to configure, defaulting to subprocess Solver")
    Solver = solver.Solver


class SolverMeta(type):
    """
    Metaclass that augments test class to set the test name
    on entry. Each function that starts with "test_" now will
    set self.test_name to be the name of the test at the beginning.
    """

    def __new__(cls, clsname, bases, attrs):
        for k, inner in attrs.items():
            if k.startswith('test_'):
                def outer(self, *, k=k, inner=inner, clsname=clsname):
                    self.test_name = k
                    if hasattr(self.solver, 'set_process_name'):
                        self.solver.set_process_name(f'python solver.py -- {clsname}::{self.test_name}')
                    inner(self)
                attrs[k] = outer
        return super().__new__(cls, clsname, bases, attrs)


class SolverCase(unittest.TestCase, metaclass=SolverMeta):

    def setUp(self):
        self.solver = None
        self.solver = Solver()
        self.solver.set(AUTO_CONFIG=False)

    def tearDown(self):
        if isinstance(self.solver, solver.Solver):
            del self.solver

    def prove(self, cond, *o, pre=None, return_model=False, minimize=True, top=True):
        assert not o
        if minimize:
            self.solver.push()

        self.solver.add(z3.Not(cond))

        if top:
            filename = f'{type(self).__name__}-{self.test_name}.smt2'
            with open(os.path.join(tempdir, filename), 'w') as f:
                f.write(str(self.solver.to_smt2()))

        res = self.solver.check()
        if res != z3.unsat:
            if not minimize and not return_model:
                self.assertEqual(res, z3.unsat)

            model = self.solver.model()
            if return_model:
                return model

            print("Could not prove, trying to find a minimal ce")
            assert res != z3.unknown
            if z3.is_and(cond):
                self.solver.pop()
                # Condition is a conjunction of some child clauses.
                # See if we can find something smaller that is sat.

                if pre is not None:
                    ccond = sorted(
                        zip(cond.children(), pre.children()), key=lambda x: len(str(x[0])))
                else:
                    ccond = sorted(cond.children(), key=lambda x: len(str(x)))

                for i in ccond:
                    self.solver.push()
                    if isinstance(i, tuple):
                        self.prove(i[0], pre=i[1], top=False)
                    else:
                        self.prove(i, top=False)
                    self.solver.pop()

            print("Can not minimize condition further")
            if pre is not None:
                print("Precondition")
                print(pre)
                print("does not imply")
            print(cond)
            self.assertEqual(model, [])


class PrintHider:
    def __enter__(self):
        self._stdout = sys.stdout
        self.f = open(os.devnull, 'w')
        sys.stdout = self.f
    def __exit__(self, *args):
        self.f.close()
        sys.stdout = self._stdout


class AsmContext(ctx.Context):
    def __init__(self, **kwargs):
        super().__init__(**kwargs)

        fields = []

        for (name, default) in fields:
            setattr(self, name, kwargs.get(name, default))

    def merge(self, cond, c1, c2):
        super().merge(cond, c1, c2)


class Lemma:

    lemmas = {}
    lemmatype = collections.namedtuple('Lemma',
        ['predicate', 'dependencies', 'name', 'implementation', 'invariant'])

    def __init__(self, *, implementation=False, invariant=False):
        self.dependencies = list()
        self.implementation = implementation
        self.invariant = invariant

    def __call__(self, fun):
        type(self).lemmas[fun.__name__] = type(self).lemmatype(
            predicate=fun,
            dependencies=self.dependencies,
            name=fun.__name__,
            implementation=self.implementation,
            invariant=self.invariant
        )
        return fun

    @classmethod
    def all_lemmas(cls, *, filter=None):
        if filter is None:
            filter = lambda *a : True
        return lambda state : \
            z3.And(*[lemma.predicate(state) for _, lemma in cls.lemmas.items() if filter(lemma)])

    @classmethod
    def lemma_with_deps(cls, name):
        """
        Return a function taking a state and returning a Z3
        expression corresponding to conjunction of the named lemma
        and all its dependencies.
        """
        found = set()
        def discover(name):
            nonlocal found
            if name not in found:
                found.add(name)
                for dep in cls.lemmas[name].dependencies:
                    discover(dep)
        discover(name)
        def newpredicate(state, *, found=found):
            return z3.And(*[cls.lemmas[name].predicate(state) for name in found])
        return newpredicate


class Specification:

    specs = {}
    spectype = collections.namedtuple('Specification',
        ['disabled', 'function', 'name', 'argnames', 'domain'])

    def __init__(self, *, disabled=False, domain=None):
        assert domain is not None
        self.disabled = disabled
        self.domain = domain

    def __call__(self, fun):
        assert fun.__name__ not in type(self).specs
        type(self).specs[fun.__name__] = type(self).spectype(
            disabled=self.disabled,
            function=fun,
            name=fun.__name__,
            domain=self.domain,
            argnames=list(inspect.signature(fun).parameters)[1:],
        )
        return fun


class Shim:

    shims = {}
    shimtype = collections.namedtuple('Shim', ['function', 'name'])

    def __init__(self):
        pass

    def __call__(self, fun):
        assert fun.__name__ not in type(self).shims
        type(self).shims[fun.__name__] = type(self).shimtype(
            function=fun,
            name=fun.__name__,
        )
        return fun

    @classmethod
    def add_shims(cls, ctx):
        for name, shim in cls.shims.items():
            pattern = re.compile(f'@{name}(_\\d+)?')
            for global_name in ctx.globals:
                if pattern.match(global_name):
                    ctx.globals[global_name] = shim.function
            ctx.globals[f'@{name}'] = shim.function
