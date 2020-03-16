import re, unittest, time
import os, signal
import asyncio
from asyncio.subprocess import DEVNULL, PIPE
from pathlib import Path

TIMEOUT = 10
TESTDIR = ['o.x86_64/', 'o.x86_64/tests/', 'tests/']

def kernel(name, **kwargs):
    def _kernel(f):
        def path(name):
            try:
                return next(x + name for x in TESTDIR if Path(x + name).is_file())
            except StopIteration:
                raise FileNotFoundError(f'Kernel {name} not found.')
        def _wrap(self):
            cmd = 'make %s KERNEL=%s' % (kwargs.get('target', 'qemu'), path(name))
            if 'append' in kwargs:
                cmd = cmd + ' APPEND="%s"' % (kwargs['append'],)
            if 'initrd' in kwargs:
                cmd = cmd + ' INITRD=%s' % (path(kwargs['initrd']),)
            create = asyncio.create_subprocess_shell(cmd, stdin=PIPE, stdout=PIPE, stderr=DEVNULL, preexec_fn=os.setsid)
            self.proc = self.loop.run_until_complete(create)
            return f(self)
        return _wrap
    return _kernel


class KernelTestCase(unittest.TestCase):
    def setUp(self):
        self.loop = asyncio.get_event_loop()
        self.output = []

    def tearDown(self):
        # kill shell, make, qemu, etc.
        try:
            # try not to use SIGKILL
            os.killpg(os.getpgid(self.proc.pid), signal.SIGTERM)
        except:
            pass
        self.loop.run_until_complete(self.proc.wait())

    async def _assertOutput(self, regex):
        while True:
            try:
                line = await asyncio.wait_for(self.proc.stdout.readline(), TIMEOUT)
            except asyncio.TimeoutError:
                break
            else:
                if not line:
                    break
                line = line.decode().rstrip('\n')
                # remove ansi escape
                line = re.sub(r'\x1b[^m]*m', '', line)
                self.output.append(line)
                if re.search(regex, line):
                    return
        msg = '`%s\' not found in output:\n...\n%s' % (regex, '\n'.join(self.output[-10:]))
        self.fail(msg)

    def assertOutput(self, regex):
        self.loop.run_until_complete(self._assertOutput(regex))

    def input(self, s):
        if isinstance(s, str):
            s = s.encode()
        self.proc.stdin.write(s)


class KernelTestResult(unittest.TestResult):
    def __init__(self, stream, descriptions, verbosity):
        super().__init__(stream, descriptions, verbosity)
        self.stream = stream
        self.passes = 0
        self.green = '\x1b[32;1m'
        self.red = '\x1b[31;1m'
        self.reset = '\x1b[0m'

    def getDescription(self, test):
        (cls, meth) = test.id().split('.')[-2:]
        if meth.startswith('test_'):
            meth = meth[5:]
        return '.'.join([cls, meth])

    def startTestRun(self):
        n = self.testSuite.countTestCases()
        self.stream.writeln('%s[==========]%s Running %d test%s' % (self.green, self.reset, n, n != 1 and 's' or ''))
        self.startTestSuiteTime = time.time()

    def startTest(self, test):
        super().startTest(test)
        self.stream.writeln('%s[ RUN      ]%s %s' % (self.green, self.reset, self.getDescription(test)))
        self.startTestTime = time.time()

    def addSuccess(self, test):
        super().addSuccess(test)
        timeTaken = time.time() - self.startTestTime
        self.passes += 1
        self.stream.writeln('%s[       OK ]%s %s (%.3fs)' % (self.green, self.reset, self.getDescription(test), timeTaken))

    def addError(self, test, err):
        self.addFailure(test, err)

    def addFailure(self, test, err):
        super().addFailure(test, err)
        timeTaken = time.time() - self.startTestTime
        self.stream.writeln('%s' % self.failures[-1][1])
        self.stream.writeln('%s[  FAILED  ]%s %s (%.3fs)' % (self.red, self.reset, self.getDescription(test), timeTaken))

    def printErrors(self):
        n = self.testSuite.countTestCases()
        timeTaken = time.time() - self.startTestSuiteTime
        self.stream.writeln('%s[==========]%s %d test%s ran (%.3fs)' % (self.green, self.reset, n, n != 1 and 's' or '', timeTaken))
        self.stream.writeln('%s[  PASSED  ]%s %d test%s' % (self.green, self.reset, self.passes, self.passes != 1 and 's' or ''))
        if self.failures:
            self.stream.writeln('%s[  FAILED  ]%s %d test%s, listed below:' % (self.red, self.reset, len(self.failures), len(self.failures) != 1 and 's' or ''))
            for test, err in self.failures:
                self.stream.writeln('%s[  FAILED  ]%s %s ' % (self.red, self.reset, self.getDescription(test)))


class KernelTestRunner(unittest.TextTestRunner):
    resultclass = KernelTestResult

    def run(self, test):
        self.resultclass.testSuite = test
        return super().run(test)
