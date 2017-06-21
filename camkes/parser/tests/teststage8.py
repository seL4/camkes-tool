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

import os, sys, unittest

ME = os.path.abspath(__file__)

# Make CAmkES importable
sys.path.append(os.path.join(os.path.dirname(ME), '../../..'))

from camkes.internal.tests.utils import CAmkESTest
from camkes.parser.stage0 import Reader
from camkes.parser.stage1 import Parse1
from camkes.parser.stage2 import Parse2
from camkes.parser.stage3 import Parse3
from camkes.parser.stage4 import Parse4
from camkes.parser.stage5 import Parse5
from camkes.parser.stage6 import Parse6
from camkes.parser.stage7 import Parse7
from camkes.parser.stage8 import Parse8

class TestStage8(CAmkESTest):
    def setUp(self):
        super(TestStage8, self).setUp()
        r = Reader()
        s1 = Parse1(r)
        s2 = Parse2(s1)
        s3 = Parse3(s2, debug=True)
        s4 = Parse4(s3)
        s5 = Parse5(s4)
        s6 = Parse6(s5)
        s7 = Parse7(s6)
        self.parser = Parse8(s7)

    def test_attribute_reference(self):
        ast, _ = self.parser.parse_string('''
            connector C {
                from Procedure;
                to Procedure;
            }
            procedure P {
            }
            component Foo {
                attribute string t;
            }
            component Bar {
                attribute string s;
                provides P p;
                composition {
                    component Foo f;
                }
                configuration {
                    f.t <- s;
                }
            }
            component Baz {
                uses P p;
            }
            assembly {
                composition {
                    component Bar b1;
                    component Baz b2;
                    connection C c(from b2.p, to b1.p);
                }
                configuration {
                    b1.s = "hello world";
                }
            }
            ''')

        self.assertLen(ast.items, 6)
        C, P, Foo, Bar, Baz, assembly = ast.items

        self.assertLen(assembly.configuration.settings, 2)

        s1, s2 = assembly.configuration.settings

        self.assertEqual(s1.instance, 'b1')
        self.assertEqual(s1.attribute, 's')
        self.assertEqual(s1.value, 'hello world')

        self.assertEqual(s2.instance, 'b1.f')
        self.assertEqual(s2.attribute, 't')
        self.assertEqual(s2.value, 'hello world')

if __name__ == '__main__':
    unittest.main()
