from __future__ import absolute_import

import sys
import argparse
import unittest

import z3

from . import newctx
from . import solver


class IrpyTestCase(unittest.TestCase):
    INTERACTIVE = False
    MODEL_HI = False
    Solver = solver.Solver

    def _solve(self, cond):
        self.solver.push()
        self.solver.add(cond)

        res = self.solver.check()
        if res == z3.sat:
            m = self.solver.model()
        self.solver.pop()
        self.assertEquals(res, z3.sat)
        return m

    def _assert(self, cond, return_model=False):
        self.solver.push()
        self.solver.add(z3.Not(cond))

        res = self.solver.check()
        model = None
        if res != z3.unsat:
            model = self.solver.model()

        self.solver.pop()

        if return_model:
            return model

        self.assertEqual(model, None)

    def _prove(self, cond, pre=None, return_model=False, minimize=True):
        if minimize:
            self.solver.push()
        self.solver.add(z3.Not(cond))

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
                        self._prove(i[0], pre=i[1])
                    else:
                        self._prove(i)
                    self.solver.pop()

            print("Can not minimize condition further")
            if pre is not None:
                print("Precondition")
                print(pre)
                print("does not imply")
            print(cond)
            self.assertEqual(model, [])

    def setUp(self):
        self.ctx = newctx()
        self.solver = self.Solver()
        self.solver.set(AUTO_CONFIG=False)
        self._set_name()

    def tearDown(self):
        if isinstance(self.solver, solver.Solver):
            del self.solver

    def _set_name(self):
        """Append class and test name to solver's proc title (if available)"""

        if hasattr(self.solver, 'get_process_name'):
            prefix = ' '.join(self.solver.get_process_name().split()[:2])
        else:
            prefix = "python solver.py"

        if hasattr(self.solver, 'set_process_name'):
            cls = self.__class__.__name__
            self.solver.set_process_name('{} -- {}::{}'.format(prefix, cls, self._testMethodName))


def main():
    parser = argparse.ArgumentParser()

    parser.add_argument('--interactive', type=bool, nargs='?',
            default=IrpyTestCase.INTERACTIVE, const=True)
    parser.add_argument('--model-hi', type=bool, nargs='?',
            default=IrpyTestCase.MODEL_HI, const=True)
    args, unknown = parser.parse_known_args(sys.argv)

    INTERACTIVE = args.interactive
    MODEL_HI = args.model_hi

    del sys.argv[:]
    sys.argv.extend(unknown)

    if INTERACTIVE:
        IrpyTestCase.Solver = z3.Solver

    print("Using z3 v" + '.'.join(map(str, z3.get_version())))

    IrpyTestCase.INTERACTIVE = INTERACTIVE
    IrpyTestCase.MODEL_HI = MODEL_HI

    unittest.main()
