#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
# Copyright 2022, Technology Innovation Institute
#
# SPDX-License-Identifier: BSD-2-Clause
#
#

from __future__ import absolute_import, division, print_function, unicode_literals

from camkes.parser import ParseError, DtbMatchQuery
from camkes.internal.tests.utils import CAmkESTest
import os
import sys
import unittest

ME = os.path.abspath(__file__)

# Make CAmkES importable
sys.path.append(os.path.join(os.path.dirname(ME), '../../..'))


class TestDTBMatchQueryRanges(CAmkESTest):
    def setUp(self):
        super(TestDTBMatchQueryRanges, self).setUp()
        self.dtbQuery = DtbMatchQuery()
        self.dtbQuery.parse_args(['--dtb', os.path.join(os.path.dirname(ME), "test_rpi4.dtb")])
        self.dtbQuery.check_options()
        self.dtbSize = os.path.getsize(os.path.join(os.path.dirname(ME), "test_rpi4.dtb"))
        self.maxDiff = None

    def test_ranges_first_index(self):
        node = self.dtbQuery.resolve([{'path': '.*cprman.*'}])
        self.assertIsInstance(node, dict)

        expected = {
            'compatible': ["brcm,bcm2711-cprman"],
			'#clock-cells': [0x01],
            'clocks': [0x03, 0x04, 0x00, 0x04, 0x01, 0x04, 0x02, 0x05, 0x00, 0x05, 0x01, 0x05, 0x02],
            'reg': [0xfe101000, 0x2000],
            'this-address-cells': [0x01],
            'this-size-cells': [0x01],
            'this-node-path': "/soc/cprman@7e101000",
            'phandle': [0x06],
        }
        self.assertIn('query', node)
        self.assertIn('dtb-size', node)
        self.assertEquals(len(node['query']), 1)
        self.assertEquals(node['query'][0], expected)
        self.assertEquals(node['dtb-size'], [self.dtbSize])

    def test_ranges_last_index(self):
        node = self.dtbQuery.resolve([{'path': '.*interrupt-controller.*'}])
        self.assertIsInstance(node, dict)

        expected = {
            'compatible': ["arm,gic-400"],
            'interrupt-controller': [],
            '#interrupt-cells': [0x03],
            'reg': [0xff841000, 0x1000, 0xff842000, 0x2000, 0xff844000, 0x2000, 0xff846000, 0x2000],
            'interrupts': [0x01, 0x09, 0xf04],
            'this-address-cells': [0x01],
            'this-size-cells': [0x01],
            'this-node-path': "/soc/interrupt-controller@40041000",
            'phandle': [0x01],
        }
        self.assertIn('query', node)
        self.assertIn('dtb-size', node)
        self.assertEquals(len(node['query']), 1)
        self.assertEquals(node['query'][0], expected)
        self.assertEquals(node['dtb-size'], [self.dtbSize])


if __name__ == '__main__':
    unittest.main()
