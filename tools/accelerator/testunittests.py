#!/usr/bin/env python
# -*- coding: utf-8 -*-

#
# Copyright 2017, Data61
# Commonwealth Scientific and Industrial Research Organisation (CSIRO)
# ABN 41 687 119 230.
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(DATA61_BSD)
#

'''
Run the accelerator's unit tests.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals

import os, sys, unittest

ME = os.path.abspath(__file__)
MY_DIR = os.path.dirname(ME)

# Make CAmkES importable
sys.path.append(os.path.join(MY_DIR, '../..'))

from camkes.internal.tests.utils import CAmkESTest, which

class TestUnitTests(CAmkESTest):
    @unittest.skipIf(which('cmake') is None or which('ninja') is None, 'CMake or Ninja not found')
    def test_run_unit_tests(self):
        tmp = self.mkdtemp()
        ret, stdout, stderr = self.execute(['cmake', '-G', 'Ninja', MY_DIR],
            cwd=tmp)
        if ret != 0:
            self.fail('cmake failed:\n%s\n%s' % (stdout, stderr))
        ret, stdout, stder = self.execute(['ninja',
            'camkes-accelerator-unittests'], cwd=tmp)
        if ret != 0:
            self.fail('make failed:\n%s\n%s' % (stdout, stderr))
        ret, stdout, stder = self.execute(['ninja', 'test'], cwd=tmp)
        if ret != 0:
            self.fail('tests failed:\n%s\n%s' % (stdout, stderr))

if __name__ == '__main__':
    unittest.main()
