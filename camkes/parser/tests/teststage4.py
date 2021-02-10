#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#
#

from __future__ import absolute_import, division, print_function, \
    unicode_literals

import os, six, sys, unittest

ME = os.path.abspath(__file__)

# Make CAmkES importable
sys.path.append(os.path.join(os.path.dirname(ME), '../../..'))

from camkes.ast import Assembly, AttributeReference, Component, \
    Composition, Connection, ConnectionEnd, Connector, Group, Instance, \
    LiftedAST, Procedure, Provides, Setting, Uses
from camkes.internal.tests.utils import CAmkESTest
from camkes.parser import ParseError
from camkes.parser.stage0 import CPP, Reader
from camkes.parser.stage1 import Parse1
from camkes.parser.stage2 import Parse2
from camkes.parser.stage3 import Parse3
from camkes.parser.stage4 import Parse4

class TestStage4(CAmkESTest):
    def setUp(self):
        super(TestStage4, self).setUp()
        r = Reader()
        s1 = Parse1(r)
        s2 = Parse2(s1)
        s3 = Parse3(s2)
        self.parser = Parse4(s3)
        self.forward_parser = Parse4(s3, True)

        r = CPP()
        s1 = Parse1(r)
        s2 = Parse2(s1)
        s3 = Parse3(s2)
        self.cpp_parser = Parse4(s3)

    def test_empty_string(self):
        ast, read = self.parser.parse_string('')

        self.assertIsInstance(ast, LiftedAST)
        self.assertLen(ast.items, 0)
        self.assertLen(read, 0)

    def test_no_references(self):
        ast, _ = self.parser.parse_string('component foo {}')

        self.assertIsInstance(ast, LiftedAST)
        self.assertLen(ast.items, 1)
        component = ast.items[0]

        self.assertIsInstance(component, Component)
        self.assertEqual(component.name, 'foo')

    def test_basic_reference(self):
        ast, read = self.parser.parse_string('component Foo {}\n'
            'assembly { composition { component Foo foo; } }')

        self.assertLen(ast.items, 2)
        Foo, assembly = ast.items

        self.assertIsInstance(Foo, Component)
        self.assertIsInstance(assembly, Assembly)

        self.assertLen(assembly.composition.instances, 1)
        foo = assembly.composition.instances[0]
        self.assertEqual(foo.name, 'foo')
        self.assertEqual(foo.type, Foo)

    def test_overlapping_names(self):
        ast, read = self.parser.parse_string('component foo {}\n'
            'assembly { composition { component foo foo; } }')

        self.assertLen(ast.items, 2)
        Foo, assembly = ast.items

        self.assertIsInstance(Foo, Component)
        self.assertIsInstance(assembly, Assembly)

        self.assertLen(assembly.composition.instances, 1)
        foo = assembly.composition.instances[0]
        self.assertEqual(foo.name, 'foo')
        self.assertEqual(foo.type, Foo)

    def test_overlapping_names2(self):
        ast, read = self.parser.parse_string('''
            procedure foo { }
            component foo {}
            assembly {
                composition {
                    component foo foo;
                }
            }
            ''')

        self.assertLen(ast.items, 3)
        FooProc, FooComp, assembly = ast.items

        self.assertIsInstance(FooComp, Component)
        self.assertIsInstance(assembly, Assembly)

        self.assertLen(assembly.composition.instances, 1)
        foo = assembly.composition.instances[0]
        self.assertEqual(foo.name, 'foo')
        self.assertEqual(foo.type, FooComp)

    def test_overlapping_names3(self):
        ast, read = self.parser.parse_string('''
            component foo {}
            procedure foo { }
            assembly {
                composition {
                    component foo foo;
                }
            }
            ''')

        self.assertLen(ast.items, 3)
        FooComp, FooProc, assembly = ast.items

        self.assertIsInstance(FooComp, Component)
        self.assertIsInstance(assembly, Assembly)

        self.assertLen(assembly.composition.instances, 1)
        foo = assembly.composition.instances[0]
        self.assertEqual(foo.name, 'foo')
        self.assertEqual(foo.type, FooComp)

    def test_colliding_names(self):
        with six.assertRaisesRegex(self, ParseError,
                r'duplicate definition of Component \'foo\''):
            self.parser.parse_string('''
                component foo {}
                component foo { }
                ''')

    def test_colliding_names_and_groups(self):
        with six.assertRaisesRegex(self, ParseError,
                r'6:31: duplicate definition of group/component \'b\'; previous definition was at <unnamed>:5'):
            self.parser.parse_string('''
                component bar {}
                assembly {
                    composition {
                        component bar b;
                        group b {
                            component bar c;
                        }
                    }
                }                ''')

    def test_unresolved_reference(self):
        with six.assertRaisesRegex(self, ParseError,
                r'unknown reference to \'Foo\''):
            self.parser.parse_string('''
                component bar {}
                assembly {
                    composition {
                        component Foo foo;
                    }
                }
                ''')

    def test_unresolved_reference2(self):
        with six.assertRaisesRegex(self, ParseError,
                r'unknown reference to \'Foo\''):
            self.parser.parse_string('''
                procedure Foo {}
                assembly {
                    composition {
                        component Foo foo;
                    }
                }
                ''')

    def test_unresolved_reference3(self):
        with six.assertRaisesRegex(self, ParseError,
                r'unknown reference to \'Foo\''):
            self.parser.parse_string('''
                procedure Foo {}
                composition Foo {}
                assembly {
                    composition {
                        component Foo foo;
                    }
                }
                ''')

    def test_forward_reference(self):
        with six.assertRaisesRegex(self, ParseError,
                r'unknown reference to \'Foo\''):
            self.parser.parse_string('''
                component bar {}
                assembly {
                    composition {
                        component Foo foo;
                    }
                }
                component Foo {}
                ''')

    def test_attribute_reference(self):
        content, _ = self.parser.parse_string('''
            component B {
                attribute string b_str;
            }

            component A {
                attribute string a_str;

                composition {
                    component B b;
                }
                configuration {
                    b.b_str <- a_str;
                }
            }''')

        self.assertIsInstance(content, LiftedAST)
        self.assertLen(content.items, 2)
        A = content.items[1]

        self.assertIsInstance(A, Component)
        self.assertIsNotNone(A.configuration)
        self.assertLen(A.configuration.settings, 1)
        b_b_str = A.configuration.settings[0]

        self.assertIsInstance(b_b_str, Setting)
        self.assertIsInstance(b_b_str.value, AttributeReference)
        a_str = b_b_str.value

        self.assertEqual(a_str.reference, 'a_str')

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
        self.assertLen(comp.groups, 1)
        g = comp.groups[0]
        self.assertIsInstance(g, Group)

        self.assertLen(g.instances, 1)
        a2 = g.instances[0]
        self.assertIsInstance(a2, Instance)

        self.assertLen(comp.instances, 1)
        a1 = comp.instances[0]
        self.assertIsInstance(a1, Instance)

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

        self.assertLen(c2.from_ends, 1)
        g_a2_b = c2.from_ends[0]
        self.assertIsInstance(g_a2_b, ConnectionEnd)

        self.assertIs(g_a2_b.instance, a2)
        self.assertIs(g_a2_b.interface, b)

        self.assertLen(c2.to_ends, 1)
        a1_a = c2.to_ends[0]
        self.assertIsInstance(a1_a, ConnectionEnd)

        self.assertIs(a1_a.instance, a1)
        self.assertIs(a1_a.interface, a)

    def test_group_with_connection2(self):
        '''
        There's a slight quirk with reference resolution involving groups
        where, though you may have interleaved instances, groups and
        connections in your spec, these come out clumped together by type in
        the AST. This is usually not an issue as connections can reference
        instances and groups, but instances and groups cannot reference
        anything else. This test ensures that we get the same results as the
        previous test case with the group reordered.
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
        self.assertLen(comp.groups, 1)
        g = comp.groups[0]
        self.assertIsInstance(g, Group)

        self.assertLen(g.instances, 1)
        a2 = g.instances[0]
        self.assertIsInstance(a2, Instance)

        self.assertLen(comp.instances, 1)
        a1 = comp.instances[0]
        self.assertIsInstance(a1, Instance)

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

        self.assertLen(c2.from_ends, 1)
        g_a2_b = c2.from_ends[0]
        self.assertIsInstance(g_a2_b, ConnectionEnd)

        self.assertIs(g_a2_b.instance, a2)
        self.assertIs(g_a2_b.interface, b)

        self.assertLen(c2.to_ends, 1)
        a1_a = c2.to_ends[0]
        self.assertIsInstance(a1_a, ConnectionEnd)

        self.assertIs(a1_a.instance, a1)
        self.assertIs(a1_a.interface, a)

    def test_forward_references(self):
        spec = '''
            connector Foo {
                from Procedure;
                to Procedure;
            }
            component Client {
                uses P p; /* <- forward reference */
            }
            procedure P {
                void bar();
            }
            component Server {
                provides P p;
            }
            assembly {
                composition {
                    component Client c;
                    component Server s;
                    connection Foo f(from c.p, to s.p);
                }
            }
            '''

        # This specification should be rejected by the default parser because
        # forward references are not supported.
        with self.assertRaises(ParseError):
            self.parser.parse_string(spec)

        # This specification should be accepted by the parser that supports
        # forward references.
        content, _ = self.forward_parser.parse_string(spec)

        self.assertLen(content.items, 5)
        Foo, Client, P, Server, assembly = content.items

        self.assertIsInstance(Foo, Connector)
        self.assertIsInstance(Client, Component)
        self.assertIsInstance(P, Procedure)
        self.assertIsInstance(Server, Component)
        self.assertIsInstance(assembly, Assembly)

        self.assertLen(Client.uses, 1)
        self.assertIs(Client.uses[0].type, P)

    def test_cycles(self):
        '''
        Test that we can correctly detect and prevent cycles in the AST.
        '''
        spec = '''
            component Client {
                composition {
                    component Client c;
                }
            }
        '''
        with six.assertRaisesRegex(self, ParseError,
                r'AST cycle involving entity Client'):
            self.forward_parser.parse_string(spec)

    def test_cross_assembly_reference(self):
        '''
        Test that we can make references from one assembly to another.
        '''
        spec = '''
            connector Conn {
                from Procedure;
                to Procedure;
            }
            procedure P {
                void foo();
            }
            component Client {
                uses P p;
            }
            component Server {
                provides P p;
            }
            assembly {
                composition {
                    component Client c;
                    component Server s;
                }
            }
            assembly {
                composition {
                    connection Conn conn(from c.p, to s.p);
                }
            }'''
        content, _ = self.parser.parse_string(spec)

        self.assertLen(content.items, 6)
        Conn, P, Client, Server, a1, a2 = content.items

        self.assertLen(a1.composition.children, 2)
        c, s = a1.composition.children
        self.assertIsInstance(c, Instance)
        self.assertLen(c.type.uses, 1)
        self.assertIsInstance(s, Instance)
        self.assertLen(s.type.provides, 1)

        self.assertLen(a2.composition.children, 1)
        conn = a2.composition.children[0]
        self.assertIsInstance(conn, Connection)

        self.assertIs(conn.type, Conn)

        self.assertLen(conn.from_ends, 1)
        self.assertIs(conn.from_end.instance, c)
        self.assertIs(conn.from_end.interface, c.type.uses[0])

        self.assertLen(conn.to_ends, 1)
        self.assertIs(conn.to_end.instance, s)
        self.assertIs(conn.to_end.interface, s.type.provides[0])

    def test_cross_assembly_forward_reference(self):
        '''
        Test that we can make a reference from one assembly to a future one
        when forward references are enabled.
        '''
        spec = '''
            connector Conn {
                from Procedure;
                to Procedure;
            }
            procedure P {
                void foo();
            }
            component Client {
                uses P p;
            }
            component Server {
                provides P p;
            }
            assembly {
                composition {
                    connection Conn conn(from c.p, to s.p);
                }
            }
            assembly {
                composition {
                    component Client c;
                    component Server s;
                }
            }'''
        content, _ = self.forward_parser.parse_string(spec)

        self.assertLen(content.items, 6)
        Conn, P, Client, Server, a2, a1 = content.items

        self.assertLen(a1.composition.children, 2)
        c, s = a1.composition.children
        self.assertIsInstance(c, Instance)
        self.assertLen(c.type.uses, 1)
        self.assertIsInstance(s, Instance)
        self.assertLen(s.type.provides, 1)

        self.assertLen(a2.composition.children, 1)
        conn = a2.composition.children[0]
        self.assertIsInstance(conn, Connection)

        self.assertIs(conn.type, Conn)

        self.assertLen(conn.from_ends, 1)
        self.assertIs(conn.from_end.instance, c)
        self.assertIs(conn.from_end.interface, c.type.uses[0])

        self.assertLen(conn.to_ends, 1)
        self.assertIs(conn.to_end.instance, s)
        self.assertIs(conn.to_end.interface, s.type.provides[0])

    def test_duplicate_parameter_names(self):
        '''
        Previously, with forward resolution enabled, a ParseError would be
        incorrectly raised when you re-used a method argument name. Method
        names should essentially be meaningless to the parser and should not
        escape the method in which they are contained. This test validates that
        this bug has not been re-introduced.
        '''
        spec = '''
            procedure P {
                void foo(in int x);
                void bar(in int x);
            }
        '''

        self.parser.parse_string(spec)

        self.forward_parser.parse_string(spec)

if __name__ == '__main__':
    unittest.main()
