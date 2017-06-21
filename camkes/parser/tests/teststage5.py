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

from camkes.ast import Component, Composition, Connection, ConnectionEnd, \
    Export, Instance, Provides, Uses
from camkes.internal.tests.utils import CAmkESTest
from camkes.parser.exception import ParseError
from camkes.parser.stage0 import CPP, Reader
from camkes.parser.stage1 import Parse1
from camkes.parser.stage2 import Parse2
from camkes.parser.stage3 import Parse3
from camkes.parser.stage4 import Parse4
from camkes.parser.stage5 import Parse5

class TestStage5(CAmkESTest):
    def setUp(self):
        super(TestStage5, self).setUp()
        r = Reader()
        s1 = Parse1(r)
        s2 = Parse2(s1)
        s3 = Parse3(s2, debug=True)
        s4 = Parse4(s3)
        self.parser = Parse5(s4)

    def test_group_basic(self):
        ast, _ = self.parser.parse_string('''
            component A {}
            component B {}
            composition {
                group foo {
                    component A a;
                    component B b;
                }
            }
            ''')

        self.assertLen(ast.items, 3)
        comp = ast.items[2]

        self.assertIsInstance(comp, Composition)
        self.assertLen(comp.instances, 2)
        self.assertLen(comp.groups, 0)
        a, b = comp.instances

        self.assertIsInstance(a, Instance)
        self.assertEqual(a.address_space, 'foo')

        self.assertIsInstance(b, Instance)
        self.assertEqual(b.address_space, 'foo')

    def test_group_mixed(self):
        ast, _ = self.parser.parse_string('''
            component A {}
            composition {
                component A a1;
                group b {
                    component A a2;
                }
                component A a3;
                group c {
                    component A a4;
                }
            }
            ''')

        self.assertLen(ast.items, 2)
        comp = ast.items[1]

        self.assertIsInstance(comp, Composition)
        self.assertLen(comp.instances, 4)

        seen = set()
        for a in comp.instances:
            if a.name == 'a1':
                self.assertEqual(a.address_space, 'a1')
            elif a.name == 'a2':
                self.assertEqual(a.address_space, 'b')
            elif a.name == 'a3':
                self.assertEqual(a.address_space, 'a3')
            elif a.name == 'a4':
                self.assertEqual(a.address_space, 'c')
            else:
                self.fail('unexpected instance %s found' % a.name)
            seen.add(a.name)

        self.assertLen(seen, 4, 'some expected instances not found')

    def test_group_with_connection(self):
        ast, _ = self.parser.parse_string('''
            connector Conn {
                from Procedure;
                to Procedure;
            }
            procedure P {}
            component A {
                provides P a;
                uses P b;
            }
            composition {
                component A a1;
                group g {
                    component A a2;
                }
                connection Conn c(from a1.b, to g.a2.a);
                connection Conn c2(from g.a2.b, to a1.a);
            }
            ''')

        self.assertLen(ast.items, 4)
        _, _, A, comp = ast.items

        self.assertIsInstance(A, Component)
        self.assertLen(A.provides, 1)
        a = A.provides[0]
        self.assertIsInstance(a, Provides)
        self.assertLen(A.uses, 1)
        b = A.uses[0]
        self.assertIsInstance(b, Uses)

        self.assertIsInstance(comp, Composition)

        # The group will have been collapsed, so we'll now have two instances.

        self.assertLen(comp.instances, 2)
        a1, a2 = comp.instances
        self.assertIsInstance(a1, Instance)
        self.assertIsInstance(a2, Instance)

        self.assertLen(comp.connections, 2)
        c, c2 = comp.connections
        self.assertIsInstance(c, Connection)
        self.assertIsInstance(c2, Connection)

        self.assertLen(c.from_ends, 1)
        a1_b = c.from_ends[0]
        self.assertIsInstance(a1_b, ConnectionEnd)

        self.assertIs(a1_b.instance, a1)
        self.assertIs(a1_b.interface, b)

        self.assertLen(c.to_ends, 1)
        g_a2_a = c.to_ends[0]
        self.assertIsInstance(g_a2_a, ConnectionEnd)

        self.assertIs(g_a2_a.instance, a2)
        self.assertIs(g_a2_a.interface, a)

    def test_group_with_connection2(self):
        '''
        For the purpose of this, see the identically named test case in the
        stage 4 tests.
        '''
        ast, _ = self.parser.parse_string('''
            connector Conn {
                from Procedure;
                to Procedure;
            }
            procedure P {}
            component A {
                provides P a;
                uses P b;
            }
            composition {
                group g {
                    component A a2;
                }
                component A a1;
                connection Conn c(from a1.b, to g.a2.a);
                connection Conn c2(from g.a2.b, to a1.a);
            }
            ''')

        self.assertLen(ast.items, 4)
        _, _, A, comp = ast.items

        self.assertIsInstance(A, Component)
        self.assertLen(A.provides, 1)
        a = A.provides[0]
        self.assertIsInstance(a, Provides)
        self.assertLen(A.uses, 1)
        b = A.uses[0]
        self.assertIsInstance(b, Uses)

        self.assertIsInstance(comp, Composition)

        # The group will have been collapsed, so we'll now have two instances.

        self.assertLen(comp.instances, 2)
        a1, a2 = comp.instances
        self.assertIsInstance(a1, Instance)
        self.assertIsInstance(a2, Instance)

        self.assertLen(comp.connections, 2)
        c, c2 = comp.connections
        self.assertIsInstance(c, Connection)
        self.assertIsInstance(c2, Connection)

        self.assertLen(c.from_ends, 1)
        a1_b = c.from_ends[0]
        self.assertIsInstance(a1_b, ConnectionEnd)

        self.assertIs(a1_b.instance, a1)
        self.assertIs(a1_b.interface, b)

        self.assertLen(c.to_ends, 1)
        g_a2_a = c.to_ends[0]
        self.assertIsInstance(g_a2_a, ConnectionEnd)

        self.assertIs(g_a2_a.instance, a2)
        self.assertIs(g_a2_a.interface, a)

    def test_export_reference(self):
        ast, _ = self.parser.parse_string('''
            procedure P {}
            component Foo {
                provides P a;
            }
            component Bar {
                provides P b;
                composition {
                    component Foo c;
                    export c.a -> b;
                }
            }
            ''')

        self.assertLen(ast.items, 3)
        P, Foo, Bar = ast.items

        self.assertIsInstance(Bar, Component)
        comp = Bar.composition

        self.assertIsInstance(comp, Composition)
        self.assertLen(comp.instances, 1)
        c = comp.instances[0]

        self.assertLen(comp.exports, 1)
        e = comp.exports[0]

        self.assertIsInstance(e.source_instance, Instance)
        self.assertIs(e.source_instance, c)
        self.assertIsInstance(e.source_interface, Provides)
        self.assertIs(e.source_interface, Foo.provides[0])
        self.assertIsInstance(e.destination, Provides)
        self.assertIs(e.destination, Bar.provides[0])

    def test_invalid_export(self):
        with self.assertRaises(ParseError):
            self.parser.parse_string('''
                procedure P {}
                component Foo {
                    provides P a;
                }
                composition {
                    component Foo b;
                }
                component Bar {
                    composition {
                        component Foo c;
                        export c.a -> b;
                    }
                }
                ''')

if __name__ == '__main__':
    unittest.main()
