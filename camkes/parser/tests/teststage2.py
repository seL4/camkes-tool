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

from camkes.internal.tests.utils import CAmkESTest, cpp_available
from camkes.parser.stage0 import CPP, Reader
from camkes.parser.stage1 import Parse1
from camkes.parser.stage2 import Parse2

class TestStage2(CAmkESTest):
    def setUp(self):
        super(TestStage2, self).setUp()
        r = Reader()
        s1 = Parse1(r)
        self.parser = Parse2(s1)

        r = CPP()
        s1 = Parse1(r)
        self.cpp_parser = Parse2(s1)

    def test_empty_string(self):
        content, read = self.parser.parse_string('')

        self.assertEqual(content, [])
        self.assertLen(read, 0)

    def test_basic_entity(self):
        content, read = self.parser.parse_string('component foo {}')

        self.assertLen(content, 1)
        self.assertEqual(content[0][0], 'component foo {}')
        self.assertIsNone(content[0][1])
        comp = content[0][2]

        self.assertEqual(comp.head, 'component_decl')
        self.assertLen(comp.tail, 2)
        self.assertEqual(comp.tail[0].head, 'id')
        self.assertLen(comp.tail[0].tail, 1)
        self.assertEqual(comp.tail[0].tail[0], 'foo')
        self.assertEqual(comp.tail[1].head, 'component_defn')
        self.assertLen(comp.tail[1].tail, 0)
        self.assertLen(read, 0)

    def test_malformed(self):
        with self.assertRaises(Exception):
            self.parser.parse_string('hello world')

    def test_unicode(self):
        content, read = self.parser.parse_string('component foó {}')

        self.assertLen(content, 1)
        self.assertEqual(content[0][0], 'component foó {}')
        self.assertIsNone(content[0][1])
        comp = content[0][2]

        self.assertEqual(comp.head, 'component_decl')
        self.assertLen(comp.tail, 2)
        self.assertEqual(comp.tail[0].head, 'id')
        self.assertLen(comp.tail[0].tail, 1)
        self.assertEqual(comp.tail[0].tail[0], 'foó')
        self.assertEqual(comp.tail[1].head, 'component_defn')
        self.assertLen(comp.tail[1].tail, 0)
        self.assertLen(read, 0)

    def test_from_file(self):
        tmp = self.mkstemp()
        with open(tmp, 'wt') as f:
            f.write('component foo {}')

        content, read = self.parser.parse_file(tmp)

        self.assertLen(content, 1)
        self.assertEqual(content[0][0], 'component foo {}')
        self.assertEqual(content[0][1], tmp)
        comp = content[0][2]

        self.assertEqual(comp.head, 'component_decl')
        self.assertLen(comp.tail, 2)
        self.assertEqual(comp.tail[0].head, 'id')
        self.assertLen(comp.tail[0].tail, 1)
        self.assertEqual(comp.tail[0].tail[0], 'foo')
        self.assertEqual(comp.tail[1].head, 'component_defn')
        self.assertLen(comp.tail[1].tail, 0)
        self.assertEqual(read, set([tmp]))

    @unittest.skipIf(not cpp_available(), 'CPP not found')
    def test_with_cpp(self):
        parent = self.mkstemp()
        child = self.mkstemp()

        with open(parent, 'wt') as f:
            f.write('component foo\n#include "%s"' % child)
        with open(child, 'wt') as f:
            f.write('{}')

        content, read = self.cpp_parser.parse_file(parent)

        self.assertLen(content, 1)
        self.assertEqual(content[0][1], parent)
        comp = content[0][2]

        self.assertEqual(comp.head, 'component_decl')
        self.assertLen(comp.tail, 2)
        self.assertEqual(comp.tail[0].head, 'id')
        self.assertLen(comp.tail[0].tail, 1)
        self.assertEqual(comp.tail[0].tail[0], 'foo')
        self.assertEqual(comp.tail[1].head, 'component_defn')
        self.assertLen(comp.tail[1].tail, 0)
        self.assertIn(parent, read)
        self.assertIn(child, read)

    def test_simple_spec_complete(self):
        content, _ = self.parser.parse_string('''
            procedure Hello {
                void hello(void);
            }

            component Foo {
                provides Hello h;
            }

            component Bar {
                control;
                uses Hello w;
            }

            assembly {
                composition {
                    component Foo f;
                    component Bar b;
                    connection Conn conn(from Foo.h, to Bar.w);
                }
            }
            ''')

    def test_self_import(self):
        '''
        The stage 2 parser should notice cycles in the import graph and
        automatically terminate. This case validates a trivial cycle.
        '''

        input = self.mkstemp()

        with open(input, 'wt') as f:
            f.write('''
                component Foo {}
                import "%s";
                ''' % input)

        content, read = self.parser.parse_file(input)

        self.assertLen(content, 1)
        Foo = content[0][2]
        self.assertEqual(Foo.head, 'component_decl')

        self.assertEqual(read, set([input]))

        content, read = self.cpp_parser.parse_file(input)

        self.assertLen(content, 1)
        Foo = content[0][2]
        self.assertEqual(Foo.head, 'component_decl')

        self.assertIn(input, read)

    def test_cycle_import(self):
        '''
        Similar to the previous test, but a cycle involving multiple files.
        '''

        a = self.mkstemp()
        b = self.mkstemp()
        c = self.mkstemp()

        with open(a, 'wt') as f:
            f.write('''
                component Foo {}
                import "%s";
                ''' % b)
        with open(b, 'wt') as f:
            f.write('import "%s";' % c)
        with open(c, 'wt') as f:
            f.write('import "%s";' % a)

        content, read = self.parser.parse_file(a)

        self.assertLen(content, 1)
        Foo = content[0][2]
        self.assertEqual(Foo.head, 'component_decl')

        self.assertEqual(read, set([a, b, c]))

        content, read = self.cpp_parser.parse_file(a)

        self.assertLen(content, 1)
        Foo = content[0][2]
        self.assertEqual(Foo.head, 'component_decl')

        self.assertIn(a, read)
        self.assertIn(b, read)
        self.assertIn(c, read)

if __name__ == '__main__':
    unittest.main()
