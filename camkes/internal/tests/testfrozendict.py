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

import os, sys, unittest

ME = os.path.abspath(__file__)

# Make CAmkES importable
sys.path.append(os.path.join(os.path.dirname(ME), '../../..'))

from camkes.internal.frozendict import frozendict
from camkes.internal.tests.utils import CAmkESTest

class TestFrozenDict(CAmkESTest):
    def test_construction(self):
        d = frozendict()
        self.assertIsNone(d.get('hello'))

        d = frozendict({'hello':'world'})
        self.assertEqual(d['hello'], 'world')

    def test_immutable(self):
        d = frozendict()

        with self.assertRaises(Exception):
            d['hello'] = 'world'

        d = frozendict({'hello':'world'})

        with self.assertRaises(Exception):
            d['hello'] = 'world'

if __name__ == '__main__':
    unittest.main()
