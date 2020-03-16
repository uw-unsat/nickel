#!/usr/bin/env python3

from kerneltest import *


def opensgx(cpio):
    return kernel('virtsgx.bin', initrd='virtsgx/opensgx/user/test/' + cpio + '.cpio')


class TestOpenSGX(KernelTestCase):
    @opensgx('exception-div-zero')
    def test_exception_div_zero(self):
        self.assertOutput('error_msg=divide error$')

    @opensgx('simple-epcm-rwx')
    def test_simple_epcm_rwx(self):
        self.assertOutput('error_msg=page fault$')
        self.assertOutput('cr2 = 0x40008000$')

    @opensgx('simple-global')
    def test_simple_global(self):
        self.assertOutput('^a$')
        self.assertOutput('^61$')

    @opensgx('simple-hello')
    def test_simple_hello(self):
        self.assertOutput('^hello sgx!$')

    @opensgx('simple-indirect')
    def test_simple_indirect(self):
        self.assertOutput('^Result = 1, 2$')

    @opensgx('simple-printf')
    def test_simple_printf(self):
        self.assertOutput('^Hello world!$')
        self.assertOutput('^printf test$')
        self.assertOutput('^ptr locates in 0x5000[0-9a-f]{4}$')

    @opensgx('simple-sgxlib')
    def test_simple_sgxlib(self):
        self.assertOutput('^hello world$')
        self.assertOutput('^MATCH$')
        self.assertOutput('^AAAAA world$')
        self.assertOutput('^UNMATCH$')

    @opensgx('simple-stack')
    def test_simple_stack(self):
        self.assertOutput('^test stack$')
        self.assertOutput('^value = 1$')

    @opensgx('stub')
    def test_stub(self):
        self.assertOutput('^hello world$')
        self.assertOutput('^good night$')


if __name__ == '__main__':
    unittest.main(testRunner=KernelTestRunner)
