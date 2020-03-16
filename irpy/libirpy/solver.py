import os
import sys
import subprocess
import z3
import atexit

from .popen import Popen
from . import solver_utils as sutils


CURRENT = os.path.dirname(os.path.realpath(__file__))
Z3_SERVER_FILE = os.path.join(CURRENT, "server.py")


def to_smt2(term):
    s = z3.Solver()
    s.add(term)
    return s.to_smt2()


class ModelProxy(object):
    def __init__(self, model_str, solver):
        self._model = model_str
        self._solver = solver

    def __str__(self):
        return self._model

    def __repr__(self):
        return self._model

    def evaluate(self, term):
        term = term.sexpr()
        return self._solver._call('model_evaluate', term)

    def eval(self, term):
        return self.evaluate(term)

children = []

def kill_children():
    try:
        for child in children:
            if child is not None:
                child.terminate()
    except:
        pass

atexit.register(kill_children)

class Solver(object):

    def __init__(self, args=None):
        if args is None:
            args = [sys.executable, Z3_SERVER_FILE]
        self._proc = Popen(args,
                        stdout=subprocess.PIPE,
                        stdin=subprocess.PIPE,
                        # stderr=subprocess.PIPE,
                        encoding='utf8')
        children.append(self._proc)

    def _write(self, command):
        sutils.write_cmd(self._proc.stdin, command)

    def __del__(self):
        if self._proc is None:
            return

        self._proc.__exit__(None, None, None)

    def _call(self, name, *args, **kwargs):
        self._write({'name': name, 'args': args, 'kwargs': kwargs})
        res = self._read()
        if 'return' in res:
            return res['return']
        if 'exc' in res:
            raise RuntimeError(res['exc'])

    def set_process_name(self, name):
        return self._call('set_process_name', name)

    def get_process_name(self):
        return self._call('get_process_name')

    def _read(self, **kwargs):
        return sutils.read_cmd(self._proc.stdout)

    def add(self, term):
        term = to_smt2(term)
        return self._call('add', term)

    def set(self, *args, **kwargs):
        return self._call('set', *args, **kwargs)

    def check(self):
        vals = {'sat': z3.sat, 'unsat': z3.unsat, 'unknown': z3.unknown}
        return vals.get(self._call('check'))

    def model(self):
        return ModelProxy(self._call('model'), self)

    def push(self):
        return self._call('push')

    def pop(self):
        return self._call('pop')

    def to_smt2(self):
        return self._call('to_smt2')

    def str(self):
        return self._call('str')

    def repr(self):
        return self._call('repr')
