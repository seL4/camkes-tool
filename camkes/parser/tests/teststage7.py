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

from camkes.ast import Assembly
from camkes.internal.tests.utils import CAmkESTest
from camkes.parser.stage0 import CPP, Reader
from camkes.parser.stage1 import Parse1
from camkes.parser.stage2 import Parse2
from camkes.parser.stage3 import Parse3
from camkes.parser.stage4 import Parse4
from camkes.parser.stage5 import Parse5
from camkes.parser.stage6 import Parse6
from camkes.parser.stage7 import Parse7

class TestStage7(CAmkESTest):
    def setUp(self):
        super(TestStage7, self).setUp()
        r = Reader()
        s1 = Parse1(r)
        s2 = Parse2(s1)
        s3 = Parse3(s2, debug=True)
        s4 = Parse4(s3)
        s5 = Parse5(s4)
        s6 = Parse6(s5)
        self.parser = Parse7(s6)

    def test_unreferenced_hierarchical(self):
        ast, _ = self.parser.parse_string('''
            component Foo {
            }

            component Bar {
                composition {
                    component Foo f;
                }
            }

            assembly {
                composition {
                }
            }''')

        self.assertLen(ast.items, 3)
        _, _, assembly = ast.items

        self.assertIsInstance(assembly, Assembly)
        self.assertLen(assembly.composition.instances, 0)

    def test_basic(self):
        ast, _ = self.parser.parse_string('''
            component Foo {}
            component Bar {
                composition {
                    component Foo f;
                }
            }
            assembly {
                composition {
                    component Bar b;
                }
            }''')

        self.assertLen(ast.items, 3)
        Foo, Bar, assembly = ast.items

        self.assertLen(assembly.composition.instances, 2)
        b, f = assembly.composition.instances

        self.assertEqual(b.name, 'b')
        self.assertIs(b.type, Bar)
        self.assertEqual(f.name, 'b.f')
        self.assertIs(f.type, Foo)

    def test_multiple(self):
        ast, _ = self.parser.parse_string('''
            component Foo {}
            component Bar {}
            component Baz {
                composition {
                    component Foo f;
                    component Bar b;
                }
            }
            assembly {
                composition {
                    component Baz d;
                }
            }''')

        self.assertLen(ast.items, 4)
        Foo, Bar, Baz, assembly = ast.items

        self.assertLen(assembly.composition.instances, 3)
        d, f, b = assembly.composition.instances

        self.assertEqual(d.name, 'd')
        self.assertIs(d.type, Baz)
        self.assertEqual(f.name, 'd.f')
        self.assertIs(f.type, Foo)
        self.assertEqual(b.name, 'd.b')
        self.assertIs(b.type, Bar)

    def test_multiple_instantiation(self):
        ast, _ = self.parser.parse_string('''
            component Foo {}
            component Bar {
                composition {
                    component Foo f;
                    component Foo g;
                }
            }
            assembly {
                composition {
                    component Bar b;
                }
            }''')

        self.assertLen(ast.items, 3)
        Foo, Bar, assembly = ast.items

        self.assertLen(assembly.composition.instances, 3)
        b, f, g = assembly.composition.instances

        self.assertEqual(b.name, 'b')
        self.assertIs(b.type, Bar)
        self.assertEqual(f.name, 'b.f')
        self.assertIs(f.type, Foo)
        self.assertEqual(g.name, 'b.g')
        self.assertIs(g.type, Foo)

    def test_names_distinct(self):
        ast, _ = self.parser.parse_string('''
            component Foo {}
            component Bar {
                composition {
                    component Foo b;
                }
            }
            assembly {
                composition {
                    component Bar b;
                }
            }''')

        self.assertLen(ast.items, 3)
        Foo, Bar, assembly = ast.items

        self.assertLen(assembly.composition.instances, 2)
        b, f = assembly.composition.instances

        self.assertEqual(b.name, 'b')
        self.assertIs(b.type, Bar)
        self.assertEqual(f.name, 'b.b')
        self.assertIs(f.type, Foo)

    def test_multilevel(self):
        ast, _ = self.parser.parse_string('''
            component Foo {}
            component Bar {
                composition {
                    component Foo f;
                }
            }
            component Baz {
                composition {
                    component Bar b;
                }
            }
            assembly {
                composition {
                    component Baz d;
                }
            }''')

        self.assertLen(ast.items, 4)
        Foo, Bar, Baz, assembly = ast.items

        self.assertLen(assembly.composition.instances, 3)
        d, b, f = assembly.composition.instances

        self.assertEqual(d.name, 'd')
        self.assertIs(d.type, Baz)

        self.assertEqual(b.name, 'd.b')
        self.assertIs(b.type, Bar)

        self.assertEqual(f.name, 'd.b.f')
        self.assertIs(f.type, Foo)

    def test_diamond_like(self):
        '''
        This test probes behaviour when the same component type appears in two
        different branches of an assembly hierarchy.
        '''
        ast, _ = self.parser.parse_string('''
            component Foo {}
            component Bar {
                composition {
                    component Foo f;
                }
            }
            component Baz {
                composition {
                    component Foo f;
                }
            }
            assembly {
                composition {
                    component Bar b;
                    component Baz d;
                }
            }''')

        self.assertLen(ast.items, 4)
        Foo, Bar, Baz, assembly = ast.items

        # Despite the definitions of `Bar` and `Baz` being identical, the
        # parser should have produced distinct types for them.
        self.assertIsNot(Bar, Baz)

        self.assertLen(assembly.composition.instances, 4)
        b, d, f1, f2 = assembly.composition.instances

        self.assertEqual(b.name, 'b')
        self.assertIs(b.type, Bar)

        self.assertEqual(d.name, 'd')
        self.assertIs(d.type, Baz)

        self.assertEqual(f1.name, 'b.f')
        self.assertIs(f1.type, Foo)

        self.assertEqual(f2.name, 'd.f')
        self.assertIs(f2.type, Foo)

    def test_with_connection(self):
        ast, _ = self.parser.parse_string('''
            connector C {
                from Procedure;
                to Procedure;
            }
            procedure P {}
            component Foo {}
            component Bar {
                provides P p;
                composition {
                    component Foo f;
                }
            }
            component Baz {
                uses P p;
            }
            assembly {
                composition {
                    component Bar b;
                    component Baz d;
                    connection C c(from d.p, to b.p);
                }
            }''')

        self.assertLen(ast.items, 6)
        C, P, Foo, Bar, Baz, assembly = ast.items

        self.assertLen(assembly.composition.instances, 3)
        b, d, f = assembly.composition.instances

        self.assertEqual(b.name, 'b')
        self.assertIs(b.type, Bar)

        self.assertEqual(d.name, 'd')
        self.assertIs(d.type, Baz)

        self.assertEqual(f.name, 'b.f')
        self.assertIs(f.type, Foo)

        self.assertLen(assembly.composition.connections, 1)
        c = assembly.composition.connections[0]

        self.assertLen(c.from_ends, 1)
        self.assertLen(c.to_ends, 1)

        self.assertIs(c.from_end.instance, d)
        self.assertIs(c.from_end.interface, Baz.uses[0])
        self.assertIs(c.to_end.instance, b)
        self.assertIs(c.to_end.interface, Bar.provides[0])

    def test_with_internal_connection(self):
        ast, _ = self.parser.parse_string('''
            connector C {
                from Procedure;
                to Procedure;
            }
            procedure P {}
            component Foo {
                provides P p;
            }
            component Bar {
                uses P p;
            }
            component Baz {
                composition {
                    component Foo f;
                    component Bar b;
                    connection C c(from b.p, to f.p);
                }
            }
            assembly {
                composition {
                    component Baz d;
                }
            }''')

        self.assertLen(ast.items, 6)
        C, P, Foo, Bar, Baz, assembly = ast.items

        self.assertLen(assembly.composition.instances, 3)
        d, f, b = assembly.composition.instances

        self.assertEqual(d.name, 'd')
        self.assertIs(d.type, Baz)

        self.assertEqual(f.name, 'd.f')
        self.assertIs(f.type, Foo)

        self.assertEqual(b.name, 'd.b')
        self.assertIs(b.type, Bar)

        self.assertLen(assembly.composition.connections, 1)
        c = assembly.composition.connections[0]

        self.assertLen(c.from_ends, 1)
        self.assertLen(c.to_ends, 1)

        self.assertIs(c.from_end.instance, b)
        self.assertIs(c.from_end.interface, Bar.uses[0])
        self.assertIs(c.to_end.instance, f)
        self.assertIs(c.to_end.interface, Foo.provides[0])

    def test_basic_export(self):
        ast, _ = self.parser.parse_string('''
            connector C {
                from Procedure;
                to Procedure;
            }
            procedure P {}
            component Foo {
                provides P p;
            }
            component Bar {
                provides P p;
                composition {
                    component Foo f;
                    export f.p -> p;
                }
            }
            component Baz {
                uses P p;
            }
            assembly {
                composition {
                    component Bar b;
                    component Baz b2;
                    connection C con(from b2.p, to b.p);
                }
            }
            ''')

        self.assertLen(ast.items, 6)
        C, P, Foo, Bar, Baz, assembly = ast.items

        self.assertLen(assembly.composition.instances, 3)
        b, b2, f = assembly.composition.instances

        self.assertEqual(b.name, 'b')
        self.assertIs(b.type, Bar)
        self.assertEqual(b2.name, 'b2')
        self.assertIs(b2.type, Baz)
        self.assertEqual(f.name, 'b.f')
        self.assertIs(f.type, Foo)

        self.assertLen(assembly.composition.connections, 1)
        con = assembly.composition.connections[0]

        self.assertEqual(con.name, 'con')
        self.assertLen(con.from_ends, 1)
        self.assertLen(con.to_ends, 1)

        self.assertIs(con.from_end.instance, b2)
        self.assertIs(con.from_end.interface, Baz.uses[0])
        self.assertIs(con.to_end.instance.type, Foo)
        self.assertIs(con.to_end.interface, Foo.provides[0])

if __name__ == '__main__':
    unittest.main()
