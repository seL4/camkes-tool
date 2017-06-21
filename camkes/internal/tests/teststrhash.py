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

import codecs, os, subprocess, sys, unittest

ME = os.path.abspath(__file__)

# Make CAmkES importable
sys.path.append(os.path.join(os.path.dirname(ME), '../../..'))

from camkes.internal.strhash import hash_string
from camkes.internal.tests.utils import CAmkESTest, sha256sum_available, which

class TestStringHash(CAmkESTest):
    def sha256(self, data):
        assert which('sha256sum') is not None
        tmp = self.mkstemp()
        with codecs.open(tmp, 'w', 'utf-8') as f:
            f.write(data)
        sha = subprocess.check_output(['sha256sum', tmp],
            universal_newlines=True).split(' ')[0]
        return sha

    @unittest.skipIf(not sha256sum_available(), 'sha256sum not found')
    def test_hash_empty(self):
        sha1 = self.sha256('')
        sha2 = hash_string('')

        self.assertEqual(sha1, sha2)

    @unittest.skipIf(not sha256sum_available(), 'sha256sum not found')
    def test_hash_basic(self):
        sha1 = self.sha256('hello world')
        sha2 = hash_string('hello world')

        self.assertEqual(sha1, sha2)

    @unittest.skipIf(not sha256sum_available(), 'sha256sum not found')
    def test_strange_bytes(self):
        sha1 = self.sha256('hello \x43world')
        sha2 = hash_string('hello \x43world')

        self.assertEqual(sha1, sha2)

if __name__ == '__main__':
    unittest.main()
