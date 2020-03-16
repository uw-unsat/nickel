import os
import subprocess
import unittest
import random

import z3
import libirpy
import libirpy.util
from libirpy.popen import Popen

_prefix = 'o.x86_64/irpy/test'

_tests = [
    ('add', 32, 32),
    ('add_overflow_check', 32, 32),
    ('lsh', 32, (32, 0, 31)),
    ('rsh', 32, (32, 0, 31)),
    ('srem', 32, 32),
    ('urem', 32, 32),
    ('sdiv', 32, 32),
    ('udiv', 32, 32),
    ('loop2', 64, 64),
    ('loop3', 64),
    ('loop4', 64),
    ('struct_', 64),
    ('struct_t', 64, 64),
    ('array_test', 32),
    ('array_test2', 32),
    ('trunc', 64),
    ('zext', 8),
    ('sext', 8),
    ('cond', 32, 32),
    ('cond2', 32, 32),
    ('cond_global', 32, 32),
    ('alloca', 32),
    ('alloca_alias', 32),
    ('ptrptr', 32, 32, 32),
    ('switch', (32, 0, 3)),
    ('switch_table', (32, 0, 11)),
    ('call_return', 64, 64),
    ('bool_zext', 32, 32),
    ('bitcast_ptr', 64),
    ('bitcast_ptr2', 64),
    ('bitcast_ptr3', 64),
]


_throw_tests = [
    ('mul_overflow', 32, 32),
    ('add_overflow', 32, 32),
    ('zero_div', 32, 32),
    ('poison_cond', 32, 32),
    ('big_shift', 32, 32),
]


# from six
def with_metaclass(meta, *bases):
    """Create a base class with a metaclass."""
    # This requires a bit of explanation: the basic idea is to make a dummy
    # metaclass for one level of class instantiation that replaces itself with
    # the actual metaclass.
    class metaclass(type):

        def __new__(cls, name, this_bases, d):
            return meta(name, bases, d)

        @classmethod
        def __prepare__(cls, name, this_bases):
            return meta.__prepare__(name, bases)
    return type.__new__(metaclass, 'temporary_class', (), {})


class IRPyTestMeta(type):
    def __new__(cls, name, parents, dct):
        cls._add_funcs(name, parents, dct)
        return super(IRPyTestMeta, cls).__new__(cls, name, parents, dct)

    @classmethod
    def _add_funcs(cls, name, parents, dct):
        for test in dct.get('tests', []):
            name = test[0]
            args = test[1:]
            dct['test_{}'.format(name)] = lambda self, name=name, args=args: \
                self._test(name, *args)
        for test in dct.get('throw_tests', []):
            name = test[0]
            args = test[1:]
            dct['test_{}'.format(name)] = lambda self, name=name, args=args: \
                self.assertRaises(AssertionError, lambda: self._test(name, *args))


class IRPyTest(with_metaclass(IRPyTestMeta, unittest.TestCase)):
    tests = _tests
    throw_tests = _throw_tests

    def _popen(self, name, *args):
        with Popen([os.path.join(_prefix, name)] + [str(s) for s in args],
                    stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    encoding='utf8') as p:
            self.assertEqual(p.wait(), 0)
            self.assertEqual(p.stderr.read(), "")
            return p.stdout.read()

    def _random_param(self, bitsize):
        if isinstance(bitsize, tuple):
            _, start, end = bitsize
        else:
            start = 0
            end = 2 ** bitsize - 1
        return random.randint(start, end)

    def _random_params(self, *args):
        return [self._random_param(i) for i in args]

    def _irpy(self, name, *args):
        module = __import__(name)
        params = []

        for i in args:
            if isinstance(i, tuple):
                i = i[0]
            params.append(libirpy.util.FreshBitVec('param', i))

        def nop(*args, **kwargs):
            pass

        ctx = libirpy.newctx()
        libirpy.initctx(ctx, module)

        ctx.globals['@llvm_lifetime_start'] = nop
        ctx.globals['@llvm_lifetime_end'] = nop
        ctx.globals['@llvm_lifetime_start_p0i8'] = nop
        ctx.globals['@llvm_lifetime_end_p0i8'] = nop

        expr = ctx.call("@test", *params)
        return expr, params

    def _test_o(self, bin_name, py_name, *args):
        params = self._random_params(*args)
        expected = int(self._popen(bin_name, *params).strip())
        smt, symbolic_params = self._irpy(py_name, *args)

        subst = []

        for v, sym in zip(params, symbolic_params):
            subst.append((sym, z3.BitVecVal(v, sym.size())))

        res = z3.simplify(z3.substitute(smt, subst))

        assert not res.is_poison(), "Result {!r} is poison".format(res)
        self.assertEqual(res.as_long(), expected)

    def _test(self, name, *args):
        self._test_o(name, name + '_0', *args)
        self._test_o(name, name + '_1', *args)
        self._test_o(name, name + '_2', *args)


if __name__ == '__main__':
    seed = random.randint(0, 2 ** 64 - 1)
    print(("Random seed: " + str(seed)))
    random.seed(seed)
    unittest.main()
