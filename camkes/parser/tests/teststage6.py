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

import os, six, sys, unittest

ME = os.path.abspath(__file__)

# Make CAmkES importable
sys.path.append(os.path.join(os.path.dirname(ME), '../../..'))

from camkes.ast import Assembly, Component, Instance
from camkes.internal.tests.utils import CAmkESTest
from camkes.parser.stage0 import CPP, Reader
from camkes.parser.stage1 import Parse1
from camkes.parser.stage2 import Parse2
from camkes.parser.stage3 import Parse3
from camkes.parser.stage4 import Parse4
from camkes.parser.stage5 import Parse5
from camkes.parser.stage6 import Parse6

class TestStage6(CAmkESTest):
    def setUp(self):
        super(TestStage6, self).setUp()
        r = Reader()
        s1 = Parse1(r)
        s2 = Parse2(s1)
        s3 = Parse3(s2, debug=True)
        s4 = Parse4(s3)
        s5 = Parse5(s4)
        self.parser = Parse6(s5)

    def test_basic(self):
        ast, _ = self.parser.parse_string('''
            component A {}
            assembly {
                composition {
                    component A a;
                    component A b;
                }
            }
            ''')

        self.assertLen(ast.items, 2)
        A, assembly = ast.items

        self.assertIsInstance(A, Component)
        self.assertIsInstance(assembly, Assembly)

    def test_assembly_combining_basic(self):
        ast, _ = self.parser.parse_string('''
            component A {}
            assembly ass {
                composition {
                    component A a;
                }
            }
            assembly ass2 {
                composition {
                    component A b;
                }
            }
            ''')

        self.assertLen(ast.items, 2)
        A, ass = ast.items

        self.assertIsInstance(A, Component)
        self.assertIsInstance(ass, Assembly)
        self.assertEqual(ass.name, 'ass')

        self.assertLen(ass.composition.instances, 2)
        a, b = ass.composition.instances

        self.assertIsInstance(a, Instance)
        self.assertEqual(a.name, 'a')

        self.assertIsInstance(b, Instance)
        self.assertEqual(b.name, 'b')

    def test_assembly_combining_with_groups(self):
        ast, _ = self.parser.parse_string('''
            component A {}
            assembly ass {
                composition {
                    group {
                        component A a;
                    }
                }
            }
            assembly ass2 {
                composition {
                    group foo {
                        component A b;
                    }
                }
            }
            ''')

        self.assertLen(ast.items, 2)
        A, ass = ast.items

        self.assertIsInstance(A, Component)
        self.assertIsInstance(ass, Assembly)
        self.assertEqual(ass.name, 'ass')

        self.assertLen(ass.composition.instances, 2)
        a, b = ass.composition.instances

        self.assertIsInstance(a, Instance)
        self.assertEqual(a.name, 'a')
        six.assertRegex(self, a.address_space, r'^unamed_group_.*$')

        self.assertIsInstance(b, Instance)
        self.assertEqual(b.name, 'b')
        self.assertEqual(b.address_space, 'foo')

    def test_assembly_line_numbering(self):
        ast, _ = self.parser.parse_string('''

            assembly A {
                composition {}
            }

            assembly B {
                composition {}
            }
            ''')

        self.assertLen(ast.items, 1)
        A = ast.items[0]

        self.assertIsInstance(A, Assembly)
        self.assertEqual(A.lineno, 3)

if __name__ == '__main__':
    unittest.main()
