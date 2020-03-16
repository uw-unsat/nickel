#!/usr/bin/env python3

from kerneltest import *

class TestKomodo(KernelTestCase):

    @kernel('monitor/ld.bin', initrd='monitor/ld/user/initrd.cpio', append='sparetest')
    def test_sparetest(self):
        self.assertOutput('sparetest complete')
        self.assertOutput('Enclave destroyed')

    @kernel('monitor/ld.bin', initrd='monitor/ld/user/initrd.cpio', append='sharetest')
    def test_sharetest(self):
        self.assertOutput('secret is Hello!')

if __name__ == '__main__':
    unittest.main(testRunner=KernelTestRunner)
