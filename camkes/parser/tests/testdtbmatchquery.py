#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
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


class TestDTBMatchQuery(CAmkESTest):
    '''
    As part of the changes brought by the new seL4DTBHardware connector,
    the DTB dictionary now includes keys 'this-address-cells' and 'this-size-cells'.
    The keys describe the number of cells required to express those particular fields in
    the 'reg' property of the DTB.

    As part of the changes brought by exposing the DTB to CAmkES userland, the DTB dictionary
    now includes a 'dtb_size' key. This key-value pair describes the size of the DTB, in bytes.
    '''

    def setUp(self):
        super(TestDTBMatchQuery, self).setUp()
        self.dtbQuery = DtbMatchQuery()
        self.dtbQuery.parse_args(['--dtb', os.path.join(os.path.dirname(ME), "test.dtb")])
        self.dtbQuery.check_options()
        self.dtbSize = os.path.getsize(os.path.join(os.path.dirname(ME), "test.dtb"))

    def test_aliases(self):
        node = self.dtbQuery.resolve([{'aliases': 'usbphy0'}])
        self.assertIsInstance(node, dict)

        expected = {
            'compatible': ["fsl,imx6q-usbphy", "fsl,imx23-usbphy"],
            'reg': [0x20c9000, 0x1000],
            'interrupts': [0x0, 0x2c, 0x4],
            'clocks': [0x4, 0xb6],
            'fsl,anatop': [0x2],
            'phandle': [0x2c],
            'this-address-cells': [0x1],
            'this-size-cells': [0x1],
            'this-node-path': "/soc/aips-bus@2000000/usbphy@20c9000",
        }
        self.assertIn('query', node)
        self.assertIn('dtb-size', node)
        self.assertEquals(len(node['query']), 1)
        self.assertEquals(node['query'][0], expected)
        self.assertEquals(node['dtb-size'], [self.dtbSize])

        node = self.dtbQuery.resolve([{'aliases': 'spi4'}])
        expected = {
            '#address-cells': [0x1],
            '#size-cells': [0x0],
            'compatible': ["fsl,imx6q-ecspi", "fsl,imx51-ecspi"],
            'reg': [0x2018000, 0x4000],
            'interrupts': [0x0, 0x23, 0x4],
            'clocks': [0x4, 0x74, 0x4, 0x74],
            'clock-names': ["ipg", "per"],
            'dmas': [0x17, 0xb, 0x8, 0x1, 0x17, 0xc, 0x8, 0x2],
            'dma-names': ["rx", "tx"],
            'status': ["disabled"],
            'this-address-cells': [0x1],
            'this-size-cells': [0x1],
            'this-node-path': "/soc/aips-bus@2000000/spba-bus@2000000/ecspi@2018000",
        }

        self.assertIn('query', node)
        self.assertEquals(node['query'][0], expected)
        self.assertEquals(len(node['query']), 1)
        self.assertEquals(node['dtb-size'], [self.dtbSize])

    def test_paths(self):
        node = self.dtbQuery.resolve([{'path': "temp"}])
        expected = {
            'compatible': ["fsl,imx6q-tempmon"],
            'interrupt-parent': [0x1],
            'interrupts': [0x0, 0x31, 0x4],
            'fsl,tempmon': [0x2],
            'fsl,tempmon-data': [0x3],
            'clocks': [0x4, 0xac],
            'this-address-cells': [0x1],
            'this-size-cells': [0x1],
            'this-node-path': "/tempmon",
        }
        self.assertIn('query', node)
        self.assertEquals(len(node['query']), 1)
        self.assertEquals(node['query'][0], expected)

        node = self.dtbQuery.resolve([{'path': '.*serial.*'}])
        expected = {
            'compatible': ["fsl,imx6q-uart", "fsl,imx21-uart"],
            'reg': [0x2020000, 0x4000],
            'interrupts': [0x0, 0x1a, 0x4],
            'clocks': [0x4, 0xa0, 0x4, 0xa1],
            'clock-names': ["ipg", "per"],
            'dmas': [0x17, 0x19, 0x4, 0x0, 0x17, 0x1a, 0x4, 0x0],
            'dma-names': ["rx", "tx"],
            'status': ["okay"],
            'pinctrl-names': ["default"],
            'pinctrl-0': [0x1a],
            'this-address-cells': [0x1],
            'this-size-cells': [0x1],
            'this-node-path': "/soc/aips-bus@2000000/spba-bus@2000000/serial@2020000",
        }
        self.assertIn('query', node)
        self.assertEquals(len(node['query']), 1)
        self.assertEquals(node['query'][0], expected)
        self.assertEquals(node['dtb-size'], [self.dtbSize])

        node = self.dtbQuery.resolve([{'path': '.*sgtl5000.*'}])
        expected = {
            'compatible': ["fsl,sgtl5000"],
            'reg': [0x0a],
            'clocks': [0x04, 0xc9],
            'VDDA-supply': [0x39],
            'VDDIO-supply': [0x35],
            'phandle': [0x78],
            'this-address-cells': [0x01],
            'this-size-cells': [0x00],
            'this-node-path': "/soc/aips-bus@2100000/i2c@21a0000/sgtl5000@a",
        }
        self.assertIn('query', node)
        self.assertEquals(len(node['query']), 1)
        self.assertEquals(node['query'][0], expected)
        self.assertEquals(node['dtb-size'], [self.dtbSize])

    def test_multiple_queries(self):
        node = self.dtbQuery.resolve([{'path': "temp"}, {'aliases': 'spi4'}])
        expected = [
            {
                'compatible': ["fsl,imx6q-tempmon"],
                'interrupt-parent': [0x1],
                'interrupts': [0x0, 0x31, 0x4],
                'fsl,tempmon': [0x2],
                'fsl,tempmon-data': [0x3],
                'clocks': [0x4, 0xac],
                'this-address-cells': [0x1],
                'this-size-cells': [0x1],
                'this-node-path': "/tempmon",
            },
            {
                '#address-cells': [0x1],
                '#size-cells': [0x0],
                'compatible': ["fsl,imx6q-ecspi", "fsl,imx51-ecspi"],
                'reg': [0x2018000, 0x4000],
                'interrupts': [0x0, 0x23, 0x4],
                'clocks': [0x4, 0x74, 0x4, 0x74],
                'clock-names': ["ipg", "per"],
                'dmas': [0x17, 0xb, 0x8, 0x1, 0x17, 0xc, 0x8, 0x2],
                'dma-names': ["rx", "tx"],
                'status': ["disabled"],
                'this-address-cells': [0x1],
                'this-size-cells': [0x1],
                'this-node-path': "/soc/aips-bus@2000000/spba-bus@2000000/ecspi@2018000",
            }
        ]
        self.assertIn('query', node)
        self.assertEquals(len(node['query']), 2)
        self.assertEquals(node['query'][0], expected[0])
        self.assertEquals(node['query'][1], expected[1])

        node = self.dtbQuery.resolve(
            [{'path': '.*sgtl5000.*'}, {'properties': {'reg[0]': 0x2020000}}])
        expected = [
            {
                'compatible': ["fsl,sgtl5000"],
                'reg': [0x0a],
                'clocks': [0x04, 0xc9],
                'VDDA-supply': [0x39],
                'VDDIO-supply': [0x35],
                'phandle': [0x78],
                'this-address-cells': [0x01],
                'this-size-cells': [0x00],
                'this-node-path': "/soc/aips-bus@2100000/i2c@21a0000/sgtl5000@a",
            },
            {
                'dma-names': ['rx', 'tx'],
                'status': ['okay'],
                'clock-names': ['ipg', 'per'],
                'interrupts': [0, 26, 4],
                'pinctrl-names': ['default'],
                'compatible': ['fsl,imx6q-uart', 'fsl,imx21-uart'],
                'dmas': [23, 25, 4, 0, 23, 26, 4, 0],
                'clocks': [4, 160, 4, 161],
                'pinctrl-0': [26],
                'reg': [33685504, 16384],
                'this-address-cells': [0x1],
                'this-size-cells': [0x1],
                'this-node-path': "/soc/aips-bus@2000000/spba-bus@2000000/serial@2020000",
            }
        ]
        self.assertIn('query', node)
        self.assertEquals(len(node['query']), 2)
        self.assertEquals(node['query'][0], expected[0])
        self.assertEquals(node['query'][1], expected[1])
        self.assertEquals(node['dtb-size'], [self.dtbSize])

    def test_blank(self):
        self.assertRaises(ParseError, self.dtbQuery.resolve, [])

    def test_blank_query(self):
        node = self.dtbQuery.resolve([{}])
        self.assertIn('query', node)
        self.assertEquals(len(node['query']), 1)
        self.assertEquals(node['query'][0], {})

    def test_properties_lvalue_index(self):
        node = self.dtbQuery.resolve([{'properties': {'reg[0]': 0x2020000}}])
        expected = {
            'dma-names': ['rx', 'tx'],
            'status': ['okay'],
            'clock-names': ['ipg', 'per'],
            'interrupts': [0, 26, 4],
            'pinctrl-names': ['default'],
            'compatible': ['fsl,imx6q-uart', 'fsl,imx21-uart'],
            'dmas': [23, 25, 4, 0, 23, 26, 4, 0],
            'clocks': [4, 160, 4, 161],
            'pinctrl-0': [26],
            'reg': [33685504, 16384],
            'this-address-cells': [0x1],
            'this-size-cells': [0x1],
            'this-node-path': "/soc/aips-bus@2000000/spba-bus@2000000/serial@2020000",
        }
        self.assertIn('query', node)
        self.assertEquals(len(node['query']), 1)
        self.assertEquals(node['query'][0], expected)
        self.assertEquals(node['dtb-size'], [self.dtbSize])

        node = self.dtbQuery.resolve([{'properties': {'compatible[0]': 'fsl,imx6q-pwm'}}])
        expected = {
            'status': ['okay'],
            'pinctrl-0': [29],
            'clock-names': ['ipg', 'per'],
            'interrupts': [0, 83, 4],
            '#pwm-cells': [2],
            'pinctrl-names': ['default'],
            'compatible': ['fsl,imx6q-pwm', 'fsl,imx27-pwm'],
            'clocks': [4, 62, 4, 145],
            'phandle': [121],
            'reg': [34078720, 16384],
            'this-address-cells': [0x1],
            'this-size-cells': [0x1],
            'this-node-path': "/soc/aips-bus@2000000/pwm@2080000",
        }
        self.assertIn('query', node)
        self.assertEquals(len(node['query']), 1)
        self.assertEquals(node['query'][0], expected)
        self.assertEquals(node['dtb-size'], [self.dtbSize])

        node = self.dtbQuery.resolve([{'properties': {'compatible[0]': 'fsl,sec-v4.0-mon-rtc-lp'}}])
        expected = {
            'compatible': ['fsl,sec-v4.0-mon-rtc-lp'],
            'regmap': [0x23],
            'offset': [0x34],
            'interrupts': [0x00, 0x13, 0x04, 0x00, 0x14, 0x04],
            'this-address-cells': [0x02],
            'this-size-cells': [0x01],
            'this-node-path': "/soc/aips-bus@2000000/snvs@20cc000/snvs-rtc-lp",
        }
        self.assertIn('query', node)
        self.assertEquals(len(node['query']), 1)
        self.assertEquals(node['query'][0], expected)
        self.assertEquals(node['dtb-size'], [self.dtbSize])

    def test_properties_star_string(self):
        node = self.dtbQuery.resolve([{
            'properties':  {
                "clock-names[*]": ["di0_pll", "di1_pll", "di0_sel", "di1_sel", "di2_sel", "di3_sel", "di0", "di1"]
            }
        }])
        self.assertIn('query', node)
        self.assertEquals(len(node['query']), 1)
        query = node['query'][0]

        self.assertIn('#address-cells', query)
        self.assertEquals(query['#address-cells'], [0x1])

        self.assertIn('#size-cells', query)
        self.assertEquals(query['#size-cells'], [0x0])

        self.assertIn('compatible', query)
        self.assertEquals(query['compatible'], ["fsl,imx6q-ldb", "fsl,imx53-ldb"])

        self.assertIn('gpr', query)
        self.assertEquals(query['gpr'], [0x5])

        self.assertIn('status', query)
        self.assertEquals(query['status'], ["okay"])

        self.assertIn('clocks', query)
        self.assertEquals(query['clocks'], [0x4, 0x21, 0x4, 0x22, 0x4, 0x27, 0x4, 0x28, 0x4, 0x29, 0x4, 0x2a, 0x4, 0x87,
                                            0x4, 0x88])

        self.assertIn('clock-names', query)
        self.assertEquals(query['clock-names'], ["di0_pll", "di1_pll", "di0_sel", "di1_sel", "di2_sel", "di3_sel",
                                                 "di0", "di1"])

        self.assertIn('this-address-cells', query)
        self.assertEquals(query['this-address-cells'], [0x1])

        self.assertIn('this-size-cells', query)
        self.assertEquals(query['this-size-cells'], [0x1])

        self.assertIn('dtb-size', node)
        self.assertEquals(node['dtb-size'], [self.dtbSize])

        node = self.dtbQuery.resolve([{
            'properties': {
                "interrupt-names[*]": ["gpmi0", "gpmi1", "gpmi2", "gpmi3"]
            }
        }])
        self.assertIn('query', node)
        self.assertEquals(len(node['query']), 1)
        query = node['query'][0]

        expected = {
            'compatible': ["fsl,imx6q-dma-apbh", "fsl,imx28-dma-apbh"],
            'reg': [0x110000, 0x2000],
            'interrupts': [0x0, 0xd, 0x4, 0x0, 0xd, 0x4, 0x0, 0xd, 0x4, 0x0, 0xd, 0x4],
            'interrupt-names': ["gpmi0", "gpmi1", "gpmi2", "gpmi3"],
            '#dma-cells': [0x1],
            'dma-channels': [0x4],
            'clocks': [0x4, 0x6a],
            'phandle': [0xf],
            'this-address-cells': [0x1],
            'this-size-cells': [0x1],
            'this-node-path': "/soc/dma-apbh@110000",
        }
        self.assertEquals(query, expected)
        self.assertIn('dtb-size', node)
        self.assertEquals(node['dtb-size'], [self.dtbSize])

        node = self.dtbQuery.resolve([{
            'properties': {
                "compatible[*]": ["fsl,imx6q-pcie", "snps,dw-pcie"]
            }
        }])

        self.assertIn('query', node)
        self.assertEquals(len(node['query']), 1)
        query = node['query'][0]
        expected = {
            'compatible': ["fsl,imx6q-pcie", "snps,dw-pcie"],
            'reg': [0x1ffc000, 0x4000, 0x1f00000, 0x80000],
            'reg-names': ["dbi", "config"],
            '#address-cells': [0x3],
            '#size-cells': [0x2],
            'device_type': ["pci"],
            'bus-range': [0x0, 0xff],
            'ranges': [0x81000000, 0x0, 0x0, 0x1f80000, 0x0, 0x10000, 0x82000000, 0x0, 0x1000000, 0x1000000, 0x0,
                       0xf00000],
            'num-lanes': [0x1],
            'interrupts': [0x0, 0x78, 0x4],
            'interrupt-names': ["msi"],
            '#interrupt-cells': [0x1],
            'interrupt-map-mask': [0x0, 0x0, 0x0, 0x7],
            'interrupt-map': [0x0, 0x0, 0x0, 0x1, 0x1, 0x0, 0x7b, 0x4, 0x0, 0x0, 0x0, 0x2, 0x1, 0x0, 0x7a, 0x4, 0x0,
                              0x0, 0x0, 0x3, 0x1, 0x0, 0x79, 0x4, 0x0, 0x0, 0x0, 0x4, 0x1, 0x0, 0x78, 0x4],
            'clocks': [0x4, 0x90, 0x4, 0xce, 0x4, 0xbd],
            'clock-names': ["pcie", "pcie_bus", "pcie_phy"],
            'status': ["okay"],
            'this-address-cells': [0x1],
            'this-size-cells': [0x1],
            'this-node-path': "/soc/pcie@1ffc000",
        }
        self.assertEquals(query, expected)
        self.assertIn('dtb-size', node)
        self.assertEquals(node['dtb-size'], [self.dtbSize])

    def test_properties_star_word_and_byte(self):
        node = self.dtbQuery.resolve([{
            'properties': {
                "clocks[*]": [0x4, 0x98, 0x4, 0x99, 0x4, 0x97, 0x4, 0x96, 0x4, 0x95]
            }
        }])

        self.assertIn('query', node)
        self.assertEquals(len(node['query']), 1)
        query = node['query'][0]
        expected = {
            'compatible': ["fsl,imx6q-gpmi-nand"],
            '#address-cells': [0x1],
            '#size-cells': [0x1],
            'reg': [0x112000, 0x2000, 0x114000, 0x2000],
            'reg-names': ["gpmi-nand", "bch"],
            'interrupts': [0x0, 0xf, 0x4],
            'interrupt-names': ["bch"],
            'clocks': [0x4, 0x98, 0x4, 0x99, 0x4, 0x97, 0x4, 0x96, 0x4, 0x95],
            'clock-names': ["gpmi_io", "gpmi_apb", "gpmi_bch", "gpmi_bch_apb", "per1_bch"],
            'dmas': [0xf, 0x0],
            'dma-names': ["rx-tx"],
            'status': ["disabled"],
            'this-address-cells': [0x1],
            'this-size-cells': [0x1],
            'this-node-path': "/soc/gpmi-nand@112000",
        }
        self.assertEquals(query, expected)
        self.assertIn('dtb-size', node)
        self.assertEquals(node['dtb-size'], [self.dtbSize])


if __name__ == '__main__':
    unittest.main()
