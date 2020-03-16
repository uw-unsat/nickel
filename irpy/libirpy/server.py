import sys
import z3

from solver_utils import write_cmd, read_cmd

try:
    from setproctitle import setproctitle, getproctitle
except ImportError:
    # If setproctitle package is not installed just ignore set_process_name
    # requests rather than fail on a missing package.
    def setproctitle(*args, **kwargs):
        pass

    def getproctitle():
        return ""


class Server(object):
    def __init__(self):
        self._s = z3.Solver()

    def _write(self, command):
        return write_cmd(sys.stdout, command)

    def _read(self):
        return read_cmd(sys.stdin)

    def run(self):
        while True:
            self.handle_cmd()

    def handle_cmd(self):
        cmd = self._read()
        if not cmd:
            sys.exit(0)
        try:
            res = {'return': getattr(self, cmd['name'])(*cmd['args'], **cmd['kwargs'])}
        except BaseException as e:
            res = {'exc': repr(e)}
        self._write(res)

    def set_process_name(self, name):
        setproctitle(name)

    def get_process_name(self):
        return getproctitle()

    def add(self, term):
        self._s.add(z3.parse_smt2_string(term))

    def set(self, **kwargs):
        self._s.set(**{str(k): v for k, v in list(kwargs.items())})

    def check(self):
        return str(self._s.check())

    def push(self):
        return str(self._s.push())

    def pop(self):
        return str(self._s.pop())

    def model(self):
        return str(self._s.model())

    def str(self):
        return str(self._s)

    def repr(self):
        return repr(self._s)

    def to_smt2(self):
        return self._s.to_smt2()

    def model_evaluate(self, term):
        model = self._s.model()

        for t in model.decls():
            if str(t) == term:
                term = t()
                break
        return str(self._s.model().evaluate(term))


if __name__ == '__main__':
    Server().run()
