#!/usr/bin/env python3

from kerneltest import *


def nistar(cmd):
    return kernel('nistar.bin', initrd='nistar/user/initrd.cpio', append=cmd, target='qemu-kernel')


class TestNistar(KernelTestCase):
    @nistar('/bin/hello 1 2 3')
    def test_hello(self):
        self.assertOutput('^hello, world$')
        self.assertOutput('^arg 1: 1$')
        self.assertOutput('^arg 2: 2$')
        self.assertOutput('^arg 3: 3$')

    # @nistar('/bin/spawn-test 1 2 3')
    # def test_spawn(self):
    #     self.assertOutput('^Start$')
    #     self.assertOutput('^hello, world$')
    #     self.assertOutput('^arg 1: 1$')
    #     self.assertOutput('^arg 2: 2$')
    #     self.assertOutput('^arg 3: 3$')
    #     self.assertOutput('^After spawn$')

    @nistar('/bin/gate-test')
    def test_gate(self):
        self.assertOutput('^gate_test: 1337 1338$')
        self.assertOutput('^gate return: 1339$')

    @nistar('/bin/fork-test')
    def test_fork(self):
        self.assertOutput('^Child 7 8$')
        self.assertOutput('^Parent 7 8$')

    """
    @nistar('/bin/picosat /share/test.cnf')
    def test_picosat(self):
        self.assertOutput('s SATISFIABLE')
        self.assertOutput('v 1 -2 -3 -4 5 0')

    @nistar('/bin/spell ttest hello')
    def test_spell(self):
        self.assertOutput('Did you mean "test"?')
        self.assertOutput('"hello" is correct!')
    """


if __name__ == '__main__':
    unittest.main(testRunner=KernelTestRunner)
