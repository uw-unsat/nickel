#!/usr/bin/env python3

from kerneltest import *

class TestVMM(KernelTestCase):
    @kernel('hello32.elf')
    def test_hello32(self):
        self.assertOutput('^Hello from protected mode!$')

    @kernel('hello64.bin')
    def test_hello64(self):
        self.assertOutput('^Hello from long mode!$')

    @kernel('xv6/kernelmemfs')
    def test_xv6(self):
        # boot correctly
        self.assertOutput('^cpu0: starting$')
        self.assertOutput('^init: starting sh$')

        # file system
        self.input('ls\n')
        self.assertOutput('^README')
        self.assertOutput('^console')

        # run test
        self.input('usertests\n')
        self.assertOutput('^ALL TESTS PASSED$')

    @kernel('virtsgx.bin', initrd='pkg/intelsgx/HelloWorld.cpio')
    def test_intelsgx_HelloWorld(self):
        self.assertOutput('enclave initialized')
        self.assertOutput('Hello world!')

    # @kernel('buildroot/bzImage', append='console=ttyS0', initrd='buildroot/rootfs.cpio.xz')
    # def test_buildroot(self):
    #     self.assertOutput('Linux version')
    #     self.assertOutput('Welcome to Buildroot')

    @kernel('crypto.bin')
    def test_crypto(self):
        self.assertOutput('ALL TESTS PASSED')

if __name__ == '__main__':
    unittest.main(testRunner=KernelTestRunner)
