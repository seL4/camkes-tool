#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#
#

from __future__ import absolute_import, division, print_function, \
    unicode_literals

import os, six, subprocess, sys, unittest

ME = os.path.abspath(__file__)

# Make CAmkES importable
sys.path.append(os.path.join(os.path.dirname(ME), '../../..'))

from camkes.internal.tests.utils import CAmkESTest, python_available

class TestHashingAssumptions(CAmkESTest):
    '''
    Some hashing operations we perform in the AST, and on-disk caching that we
    go on to perform, relies on the hashes of certain objects being stable
    across executions. It's not clear to me from the Python documentation
    whether hashing of built-in types actually has the properties we need, so
    this test case validates our assumptions.
    '''

    def test_int(self):
        '''
        Test the hash of an `int` is just its value, which we expect.
        '''
        for i in six.moves.range(1000):
            self.assertEqual(i, hash(i),
                'hash of %d is not %d as expected' % (i, i))

    def test_bool(self):
        '''
        Test the hash of a `bool` is its integer value as expected.
        '''
        self.assertEqual(hash(True), 1)
        self.assertEqual(hash(False), 0)

if __name__ == '__main__':
    unittest.main()
