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

from __future__ import absolute_import, division, print_function, \
    unicode_literals

import os, sys, tempfile, unittest

ME = os.path.abspath(__file__)

# Make CAmkES importable
sys.path.append(os.path.join(os.path.dirname(ME), '../../..'))

from camkes.internal.tests.utils import CAmkESTest
from camkes.parser.stage0 import Reader

class TestReader(CAmkESTest):
    def setUp(self):
        super(TestReader, self).setUp()
        self.reader = Reader()

    def test_empty_string(self):
        content, read = self.reader.parse_string('')
        self.assertEqual(content, '')
        self.assertLen(read, 0)

    def test_basic_string(self):
        content, read = self.reader.parse_string('hello world')
        self.assertEqual(content, 'hello world')
        self.assertLen(read, 0)

    def test_unicode_string(self):
        content, read = self.reader.parse_string('↑hello world')
        self.assertEqual(content, '↑hello world')
        self.assertLen(read, 0)

    def test_empty_file(self):
        tmp = self.mkstemp()
        with open(tmp, 'wt') as f:
            f.write('hello world')

        content, read = self.reader.parse_file(tmp)

        self.assertEqual(content, 'hello world')
        self.assertEqual(read, set([tmp]))

    def test_unicode_file(self):
        tmp = self.mkstemp()
        with open(tmp, 'wt') as f:
            f.write('↑hello world'.encode('utf-8'))

        content, read = self.reader.parse_file(tmp)

        self.assertEqual(content, '↑hello world')
        self.assertEqual(read, set([tmp]))

    def test_non_existent_file(self):
        # Create a path that we know refers to a file that doesn't exist
        _, tmp = tempfile.mkstemp()
        os.remove(tmp)
        assert not os.path.exists(tmp)

        with self.assertRaises(IOError):
            self.reader.parse_file(tmp)

if __name__ == '__main__':
    unittest.main()
