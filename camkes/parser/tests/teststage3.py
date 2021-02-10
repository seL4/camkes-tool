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
from camkes.parser import ParseError
from camkes.parser.stage3 import DONT_LIFT, LIFT, Parse3
from camkes.parser.stage2 import Parse2
from camkes.parser.stage1 import Parse1
from camkes.parser.stage0 import CPP, Reader
from camkes.internal.tests.utils import CAmkESTest, cpp_available, \
    plyplus_introspectible
from camkes.ast import Component, Configuration, Include, LiftedAST, \
    Procedure, Setting

import os
import six
import sys
import unittest

ME = os.path.abspath(__file__)

# Make CAmkES importable
sys.path.append(os.path.join(os.path.dirname(ME), '../../..'))


class TestStage3(CAmkESTest):
    def setUp(self):
        super(TestStage3, self).setUp()
        r = Reader()
        s1 = Parse1(r)
        s2 = Parse2(s1)
        self.parser = Parse3(s2, debug=True)

        r = CPP()
        s1 = Parse1(r)
        s2 = Parse2(s1)
        self.cpp_parser = Parse3(s2, debug=True)

    def test_empty_string(self):
        content, read = self.parser.parse_string('')

        self.assertIsInstance(content, LiftedAST)
        self.assertEqual(content.children, [])
        self.assertLen(read, 0)

    def test_basic_entity(self):
        content, read = self.parser.parse_string('component foo {}')

        self.assertIsInstance(content, LiftedAST)
        self.assertLen(content.items, 1)
        comp = content.items[0]

        self.assertIsInstance(comp, Component)
        self.assertEqual(comp.name, 'foo')

    def test_malformed(self):
        with self.assertRaises(ParseError):
            self.parser.parse_string('hello world')

    def test_numerics_basic(self):
        content, read = self.parser.parse_string(
            'configuration { hello.world = 1 + 4 - 2; }')

        self.assertIsInstance(content, LiftedAST)
        self.assertLen(content.items, 1)
        conf = content.items[0]

        self.assertIsInstance(conf, Configuration)
        self.assertLen(conf.settings, 1)
        setting = conf.settings[0]

        self.assertIsInstance(setting, Setting)
        self.assertEqual(setting.instance, 'hello')
        self.assertEqual(setting.attribute, 'world')
        self.assertEqual(setting.value, 3)

    def test_numerics_precedence(self):
        content, read = self.parser.parse_string(
            'configuration { hello.world = 1 + 4 * 2; }')

        self.assertIsInstance(content, LiftedAST)
        self.assertLen(content.items, 1)
        conf = content.items[0]

        self.assertIsInstance(conf, Configuration)
        self.assertLen(conf.settings, 1)
        setting = conf.settings[0]

        self.assertIsInstance(setting, Setting)
        self.assertEqual(setting.instance, 'hello')
        self.assertEqual(setting.attribute, 'world')
        # If the following fails with `10`, you've screwed up operator
        # precedence in the grammar.
        self.assertEqual(setting.value, 9,
                         'operator precedence incorrect when constant folding')

    def test_numerics_bracketing(self):
        content, read = self.parser.parse_string(
            'configuration { hello.world = (1 + 4) * 2; }')

        self.assertIsInstance(content, LiftedAST)
        self.assertLen(content.items, 1)
        conf = content.items[0]

        self.assertIsInstance(conf, Configuration)
        self.assertLen(conf.settings, 1)
        setting = conf.settings[0]

        self.assertIsInstance(setting, Setting)
        self.assertEqual(setting.instance, 'hello')
        self.assertEqual(setting.attribute, 'world')
        self.assertEqual(setting.value, 10)

    def test_numerics_bracketing2(self):
        content, read = self.parser.parse_string(
            'configuration { hello.world = 2 * (1 + 4); }')

        self.assertIsInstance(content, LiftedAST)
        self.assertLen(content.items, 1)
        conf = content.items[0]

        self.assertIsInstance(conf, Configuration)
        self.assertLen(conf.settings, 1)
        setting = conf.settings[0]

        self.assertIsInstance(setting, Setting)
        self.assertEqual(setting.instance, 'hello')
        self.assertEqual(setting.attribute, 'world')
        self.assertEqual(setting.value, 10)

    def test_numerics_illegal_op(self):
        with self.assertRaises(ParseError):
            self.parser.parse_string(
                'configuration { hello.world = 2.0 << 1; }')

    def test_unicode(self):
        content, read = self.parser.parse_string('component foó {}')

        self.assertIsInstance(content, LiftedAST)
        self.assertLen(content.items, 1)
        comp = content.items[0]

        self.assertIsInstance(comp, Component)
        self.assertEqual(comp.name, 'foó')
        self.assertLen(read, 0)

    def test_from_file(self):
        tmp = self.mkstemp()
        with open(tmp, 'wt') as f:
            f.write('component foo {}')

        content, read = self.parser.parse_file(tmp)

        self.assertIn(tmp, read)
        self.assertIsInstance(content, LiftedAST)
        self.assertLen(content.items, 1)
        comp = content.items[0]

        self.assertIsInstance(comp, Component)
        self.assertEqual(comp.name, 'foo')
        self.assertEqual(comp.filename, tmp)

    @unittest.skipIf(not cpp_available(), 'CPP not found')
    def test_with_cpp(self):
        parent = self.mkstemp()
        child = self.mkstemp()

        with open(parent, 'wt') as f:
            f.write('component foo\n#include "%s"' % child)
        with open(child, 'wt') as f:
            f.write('{}')

        content, read = self.cpp_parser.parse_file(parent)

        self.assertIn(parent, read)
        self.assertIn(child, read)
        self.assertIsInstance(content, LiftedAST)
        self.assertLen(content.items, 1)
        comp = content.items[0]

        self.assertIsInstance(comp, Component)
        self.assertEqual(comp.name, 'foo')
        self.assertEqual(comp.filename, parent)

    def test_lineno_basic(self):
        content, _ = self.parser.parse_string('component foo {}')

        self.assertIsInstance(content, LiftedAST)
        self.assertLen(content.items, 1)
        comp = content.items[0]

        self.assertIsNone(comp.filename)
        self.assertEqual(comp.lineno, 1)

    def test_lineno_basic2(self):
        content, _ = self.parser.parse_string('\ncomponent foo {}')

        self.assertIsInstance(content, LiftedAST)
        self.assertLen(content.items, 1)
        comp = content.items[0]

        self.assertIsNone(comp.filename)
        self.assertEqual(comp.lineno, 2)

    def test_lineno_basic3(self):
        content, _ = self.parser.parse_string('component\nfoo {}')

        self.assertIsInstance(content, LiftedAST)
        self.assertLen(content.items, 1)
        comp = content.items[0]

        self.assertIsNone(comp.filename)
        self.assertIn(comp.lineno, (1, 2))

    def test_filename_in_malformed_error(self):
        tmp = self.mkstemp()
        with open(tmp, 'wt') as f:
            f.write('\nhello world')

        with six.assertRaisesRegex(self, ParseError, '%s:2:.*' % tmp):
            self.parser.parse_file(tmp)

    @unittest.skipIf(not cpp_available(), 'CPP not found')
    def test_lineno_basic_cpp(self):
        content, _ = self.cpp_parser.parse_string('component foo {}')

        self.assertIsInstance(content, LiftedAST)
        self.assertLen(content.items, 1)
        comp = content.items[0]

        self.assertEqual(comp.filename, '<stdin>')
        self.assertEqual(comp.lineno, 1)

    @unittest.skipIf(not cpp_available(), 'CPP not found')
    def test_lineno_basic2_cpp(self):
        content, _ = self.cpp_parser.parse_string('\ncomponent foo {}')

        self.assertIsInstance(content, LiftedAST)
        self.assertLen(content.items, 1)
        comp = content.items[0]

        self.assertEqual(comp.filename, '<stdin>')
        self.assertEqual(comp.lineno, 2)

    @unittest.skipIf(not cpp_available(), 'CPP not found')
    def test_lineno_basic3_cpp(self):
        content, _ = self.cpp_parser.parse_string('component\nfoo {}')

        self.assertIsInstance(content, LiftedAST)
        self.assertLen(content.items, 1)
        comp = content.items[0]

        self.assertEqual(comp.filename, '<stdin>')
        self.assertIn(comp.lineno, (1, 2))

    @unittest.skipIf(not cpp_available(), 'CPP not found')
    def test_lineno_basic4_cpp(self):
        tmp = self.mkstemp()
        with open(tmp, 'wt') as f:
            f.write('component foo {}')

        content, _ = self.cpp_parser.parse_file(tmp)

        self.assertIsInstance(content, LiftedAST)
        self.assertLen(content.items, 1)
        comp = content.items[0]

        self.assertEqual(comp.filename, tmp)
        self.assertEqual(comp.lineno, 1)

    @unittest.skipIf(not cpp_available(), 'CPP not found')
    def test_lineno_with_cpp_include(self):
        parent = self.mkstemp()
        child = self.mkstemp()

        with open(parent, 'wt') as f:
            f.write('\n#include "%s"' % child)
        with open(child, 'wt') as f:
            f.write('\ncomponent foo {}')

        content, _ = self.cpp_parser.parse_file(parent)

        self.assertIsInstance(content, LiftedAST)
        self.assertLen(content.items, 1)
        comp = content.items[0]

        self.assertEqual(comp.filename, child)
        self.assertEqual(comp.lineno, 2)

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

    @unittest.skipIf(not plyplus_introspectible(), 'plyplus internals not as '
                     'expected')
    def test_for_missing_lifters(self):
        '''
        Check that stage 3 looks comprehensive.

        The stage 3 parser is designed to translate an augmented AST into a
        lifted AST. In order to do this, it needs to have specific translation
        code for each element that may appear in plyplus' emitted AST. The
        connection between [the CAmkES grammar](../camkes.g) and the stage 3
        lifting code is necessarily informal. That is, there is no built-in
        checking mechanism that the stage 3 parser is able to handle everything
        that could appear in the AST.

        What we do in this test is use plyplus' own internal parser to examine
        the CAmkES grammar and, for each parsing rule that could generate an
        entity in the augmented AST, we check that there is corresponding code
        in the stage 3 parser to handle lifting this entity.
        '''

        # Parse the CAmkES grammar using plyplus' internals.
        from plyplus.grammar_parser import parse
        grammar = os.path.join(os.path.dirname(ME), '../camkes.g')
        with open(grammar, 'rt') as f:
            camkes_grammar = parse(f.read())

        # Every type of augmented AST entity should be either lifted by a
        # a function in the dispatch table `LIFT` or returned unmodified due to
        # an entry in `DONT_LIFT`.
        lifters = list(DONT_LIFT) + list(LIFT)

        for ruledef in camkes_grammar.select('ruledef'):

            name = ruledef.tail[0]

            if name == 'start':
                # Ignore the grammar root.
                continue

            if name.startswith('@'):
                # This rule is not intended to appear in the AST.
                continue

            if name == 'import':
                # Import statements are handled in stage 2 and never expected
                # to make it to stage 3.
                continue

            self.assertIn(name, lifters, '%s, that could appear in the AST, '
                          'does not appear to be handled by any of the lifters in stage '
                          '3' % name)

    def test_signed_int(self):
        '''
        Signed int parsing was broken in an early iteration of the parser. Test
        that we haven't re-introduced this issue.
        '''
        content, _ = self.parser.parse_string('''
            procedure P {
                void f(in signed int x);
                signed int g(void);
                signed int h(in signed int x);
            }
            ''')

        self.assertLen(content.children, 1)
        P = content.children[0]
        self.assertIsInstance(P, Procedure)

        self.assertLen(P.methods, 3)
        f, g, h = P.methods

        self.assertIsNone(f.return_type)
        self.assertLen(f.parameters, 1)
        self.assertEqual(f.parameters[0].type, 'int')

        self.assertEqual(g.return_type, 'int')
        self.assertLen(g.parameters, 0)

        self.assertEqual(h.return_type, 'int')
        self.assertLen(h.parameters, 1)
        self.assertEqual(h.parameters[0].type, 'int')

    def test_char(self):
        content, _ = self.parser.parse_string('''
            procedure P {
                void f(in char x);
                char g(void);
                char h(in char x);
            }
            ''')

        self.assertLen(content.children, 1)
        P = content.children[0]
        self.assertIsInstance(P, Procedure)

        self.assertLen(P.methods, 3)
        f, g, h = P.methods

        self.assertIsNone(f.return_type)
        self.assertLen(f.parameters, 1)
        self.assertEqual(f.parameters[0].type, 'char')

        self.assertEqual(g.return_type, 'char')
        self.assertLen(g.parameters, 0)

        self.assertEqual(h.return_type, 'char')
        self.assertLen(h.parameters, 1)
        self.assertEqual(h.parameters[0].type, 'char')

    def test_signed_char(self):
        content, _ = self.parser.parse_string('''
            procedure P {
                void f(in signed char x);
                signed char g(void);
                signed char h(in signed char x);
            }
            ''')

        self.assertLen(content.children, 1)
        P = content.children[0]
        self.assertIsInstance(P, Procedure)

        self.assertLen(P.methods, 3)
        f, g, h = P.methods

        self.assertIsNone(f.return_type)
        self.assertLen(f.parameters, 1)
        self.assertEqual(f.parameters[0].type, 'signed char')

        self.assertEqual(g.return_type, 'signed char')
        self.assertLen(g.parameters, 0)

        self.assertEqual(h.return_type, 'signed char')
        self.assertLen(h.parameters, 1)
        self.assertEqual(h.parameters[0].type, 'signed char')

    def test_unsigned_char(self):
        content, _ = self.parser.parse_string('''
            procedure P {
                void f(in unsigned char x);
                unsigned char g(void);
                unsigned char h(in unsigned char x);
            }
            ''')

        self.assertLen(content.children, 1)
        P = content.children[0]
        self.assertIsInstance(P, Procedure)

        self.assertLen(P.methods, 3)
        f, g, h = P.methods

        self.assertIsNone(f.return_type)
        self.assertLen(f.parameters, 1)
        self.assertEqual(f.parameters[0].type, 'unsigned char')

        self.assertEqual(g.return_type, 'unsigned char')
        self.assertLen(g.parameters, 0)

        self.assertEqual(h.return_type, 'unsigned char')
        self.assertLen(h.parameters, 1)
        self.assertEqual(h.parameters[0].type, 'unsigned char')

    def test_line_number_preservation(self):
        content, _ = self.parser.parse_string('''
            /* multiline comment
             * that may affect line numbering
             * if we've messed up
             */
            procedure P {}
            ''')

        self.assertLen(content.children, 1)
        P = content.children[0]
        self.assertEqual(P.lineno, 6)

    def test_illegal_import(self):
        '''
        There was a bug in an early implementation of the parser that caused
        back-to-front export statements to trigger an assertion failure. This
        test validates that these correctly trigger a parser error.
        '''
        spec_bad = '''
            component {
                composition {
                    export a -> b.c;
                }
            }
        '''

        with six.assertRaisesRegex(self, ParseError, 'illegal source in export '
                                   'statement'):
            self.parser.parse_string(spec_bad)

        spec_good = '''
            component {
                composition {
                    export a.b -> c;
                }
            }
        '''
        self.parser.parse_string(spec_good)

    def test_division_by_zero(self):
        '''
        Test that dividing by zero in a spec is correctly caught.
        '''
        with six.assertRaisesRegex(self, ParseError, 'division.*by zero'):
            self.parser.parse_string('configuration { foo.bar = 1 / 0; }')

    def test_modulo_by_zero(self):
        '''
        Test that modulo by zero in a spec is correctly caught.
        '''
        with six.assertRaisesRegex(self, ParseError, 'modulo.*by zero'):
            self.parser.parse_string('configuration { foo.bar = 1 % 0; }')

    def test_dataport_variant_syntax(self):
        '''
        Test that the syntax for variant dataports is accepted by the parser.
        '''
        spec = '''component Foo {
                dataport Buf(4000) foo;
            }'''
        self.parser.parse_string(spec)

    def test_dataport_variant_arithmetic(self):
        '''
        Test we can do arithmetic inside dataport variant specs.
        '''
        spec = '''component Foo {
                dataport Buf (123 * 45/5) foo;
            }'''
        self.parser.parse_string(spec)

    def test_flooring_division(self):
        '''
        Test that constant folding of division of two integers correctly
        produces an integer.
        '''
        content, _ = self.parser.parse_string(
            'configuration { foo.bar = 3 / 2; }')

        self.assertLen(content.children, 1)
        conf = content.children[0]
        self.assertIsInstance(conf, Configuration)

        self.assertLen(conf.settings, 1)
        s = conf.settings[0]
        self.assertIsInstance(s, Setting)

        self.assertEqual(s.instance, 'foo')
        self.assertEqual(s.attribute, 'bar')
        self.assertEqual(s.value, 1)

    def test_floating_point_division1(self):
        '''
        Test that constant folding of a division by a float produces the
        correct float result.
        '''
        content, _ = self.parser.parse_string(
            'configuration { foo.bar = 3 / 2.0; }')

        self.assertLen(content.children, 1)
        conf = content.children[0]
        self.assertIsInstance(conf, Configuration)

        self.assertLen(conf.settings, 1)
        s = conf.settings[0]
        self.assertIsInstance(s, Setting)

        self.assertEqual(s.instance, 'foo')
        self.assertEqual(s.attribute, 'bar')
        self.assertEqual(s.value, 1.5)

    def test_floating_point_division2(self):
        '''
        Test that constant folding of a division of a float produces the
        correct float result.
        '''
        content, _ = self.parser.parse_string(
            'configuration { foo.bar = 3.0 / 2; }')

        self.assertLen(content.children, 1)
        conf = content.children[0]
        self.assertIsInstance(conf, Configuration)

        self.assertLen(conf.settings, 1)
        s = conf.settings[0]
        self.assertIsInstance(s, Setting)

        self.assertEqual(s.instance, 'foo')
        self.assertEqual(s.attribute, 'bar')
        self.assertEqual(s.value, 1.5)

    def test_floating_point_division3(self):
        '''
        Test that constant folding of a division involving two floats produces
        the correct float result.
        '''
        content, _ = self.parser.parse_string(
            'configuration { foo.bar = 3.0 / 2.0; }')

        self.assertLen(content.children, 1)
        conf = content.children[0]
        self.assertIsInstance(conf, Configuration)

        self.assertLen(conf.settings, 1)
        s = conf.settings[0]
        self.assertIsInstance(s, Setting)

        self.assertEqual(s.instance, 'foo')
        self.assertEqual(s.attribute, 'bar')
        self.assertEqual(s.value, 1.5)

    def test_ternary_conditional_basic(self):
        '''
        Test that the ternary conditional works as expected.
        '''
        content, _ = self.parser.parse_string(
            'configuration { foo.bar = 1 ? 2 : 3; }')

        self.assertLen(content.children, 1)
        conf = content.children[0]
        self.assertIsInstance(conf, Configuration)

        self.assertLen(conf.settings, 1)
        s = conf.settings[0]
        self.assertIsInstance(s, Setting)

        self.assertEqual(s.instance, 'foo')
        self.assertEqual(s.attribute, 'bar')
        self.assertEqual(s.value, 2)

        content, _ = self.parser.parse_string(
            'configuration { foo.bar = 0 ? 2 : 3; }')

        self.assertLen(content.children, 1)
        conf = content.children[0]
        self.assertIsInstance(conf, Configuration)

        self.assertLen(conf.settings, 1)
        s = conf.settings[0]
        self.assertIsInstance(s, Setting)

        self.assertEqual(s.instance, 'foo')
        self.assertEqual(s.attribute, 'bar')
        self.assertEqual(s.value, 3)

    def test_ternary_conditional_extended(self):
        '''
        Test the ternary conditional with some more complicated expressions
        inside it.
        '''
        content, _ = self.parser.parse_string(
            'configuration { foo.bar = (1 || 0) ? 2 : 3; }')

        self.assertLen(content.children, 1)
        conf = content.children[0]
        self.assertIsInstance(conf, Configuration)

        self.assertLen(conf.settings, 1)
        s = conf.settings[0]
        self.assertIsInstance(s, Setting)

        self.assertEqual(s.instance, 'foo')
        self.assertEqual(s.attribute, 'bar')
        self.assertEqual(s.value, 2)

        # Look ma, no brackets.
        content, _ = self.parser.parse_string(
            'configuration { foo.bar = 1 ? 1 || 0 : 3; }')

        self.assertLen(content.children, 1)
        conf = content.children[0]
        self.assertIsInstance(conf, Configuration)

        self.assertLen(conf.settings, 1)
        s = conf.settings[0]
        self.assertIsInstance(s, Setting)

        self.assertEqual(s.instance, 'foo')
        self.assertEqual(s.attribute, 'bar')
        self.assertEqual(s.value, 1)

        content, _ = self.parser.parse_string(
            'configuration { foo.bar = 1 ? 2 : (1 || 0); }')

        self.assertLen(content.children, 1)
        conf = content.children[0]
        self.assertIsInstance(conf, Configuration)

        self.assertLen(conf.settings, 1)
        s = conf.settings[0]
        self.assertIsInstance(s, Setting)

        self.assertEqual(s.instance, 'foo')
        self.assertEqual(s.attribute, 'bar')
        self.assertEqual(s.value, 2)

    def test_ternary_conditional_nested(self):
        '''
        Test nested ternary conditionals.
        '''
        content, _ = self.parser.parse_string(
            'configuration { foo.bar = (1 ? 2 : 3) ? 4 : 5; }')

        self.assertLen(content.children, 1)
        conf = content.children[0]
        self.assertIsInstance(conf, Configuration)

        self.assertLen(conf.settings, 1)
        s = conf.settings[0]
        self.assertIsInstance(s, Setting)

        self.assertEqual(s.instance, 'foo')
        self.assertEqual(s.attribute, 'bar')
        self.assertEqual(s.value, 4)

        content, _ = self.parser.parse_string(
            'configuration { foo.bar = 1 ? 2 ? 3 : 4 : 5; }')

        self.assertLen(content.children, 1)
        conf = content.children[0]
        self.assertIsInstance(conf, Configuration)

        self.assertLen(conf.settings, 1)
        s = conf.settings[0]
        self.assertIsInstance(s, Setting)

        self.assertEqual(s.instance, 'foo')
        self.assertEqual(s.attribute, 'bar')
        self.assertEqual(s.value, 3)

        content, _ = self.parser.parse_string(
            'configuration { foo.bar = 1 ? 2 : (3 ? 4 : 5); }')

        self.assertLen(content.children, 1)
        conf = content.children[0]
        self.assertIsInstance(conf, Configuration)

        self.assertLen(conf.settings, 1)
        s = conf.settings[0]
        self.assertIsInstance(s, Setting)

        self.assertEqual(s.instance, 'foo')
        self.assertEqual(s.attribute, 'bar')
        self.assertEqual(s.value, 2)

    def test_boolean_literals_plain(self):
        '''
        Test bare boolean literals.
        '''
        content, _ = self.parser.parse_string(
            'configuration { foo.bar = true; }')

        self.assertLen(content.children, 1)
        conf = content.children[0]
        self.assertIsInstance(conf, Configuration)

        self.assertLen(conf.settings, 1)
        s = conf.settings[0]
        self.assertIsInstance(s, Setting)

        self.assertEqual(s.instance, 'foo')
        self.assertEqual(s.attribute, 'bar')
        self.assertEqual(s.value, 1)

        content, _ = self.parser.parse_string(
            'configuration { foo.bar = True; }')

        self.assertLen(content.children, 1)
        conf = content.children[0]
        self.assertIsInstance(conf, Configuration)

        self.assertLen(conf.settings, 1)
        s = conf.settings[0]
        self.assertIsInstance(s, Setting)

        self.assertEqual(s.instance, 'foo')
        self.assertEqual(s.attribute, 'bar')
        self.assertEqual(s.value, 1)

        content, _ = self.parser.parse_string(
            'configuration { foo.bar = false; }')

        self.assertLen(content.children, 1)
        conf = content.children[0]
        self.assertIsInstance(conf, Configuration)

        self.assertLen(conf.settings, 1)
        s = conf.settings[0]
        self.assertIsInstance(s, Setting)

        self.assertEqual(s.instance, 'foo')
        self.assertEqual(s.attribute, 'bar')
        self.assertEqual(s.value, 0)

        content, _ = self.parser.parse_string(
            'configuration { foo.bar = False; }')

        self.assertLen(content.children, 1)
        conf = content.children[0]
        self.assertIsInstance(conf, Configuration)

        self.assertLen(conf.settings, 1)
        s = conf.settings[0]
        self.assertIsInstance(s, Setting)

        self.assertEqual(s.instance, 'foo')
        self.assertEqual(s.attribute, 'bar')
        self.assertEqual(s.value, 0)

    def test_boolean_literals_expression(self):
        '''
        Test boolean literals within an expression.
        '''
        content, _ = self.parser.parse_string(
            'configuration { foo.bar = true || false; }')

        self.assertLen(content.children, 1)
        conf = content.children[0]
        self.assertIsInstance(conf, Configuration)

        self.assertLen(conf.settings, 1)
        s = conf.settings[0]
        self.assertIsInstance(s, Setting)

        self.assertEqual(s.instance, 'foo')
        self.assertEqual(s.attribute, 'bar')
        self.assertEqual(s.value, 1)

        content, _ = self.parser.parse_string(
            'configuration { foo.bar = true && false; }')

        self.assertLen(content.children, 1)
        conf = content.children[0]
        self.assertIsInstance(conf, Configuration)

        self.assertLen(conf.settings, 1)
        s = conf.settings[0]
        self.assertIsInstance(s, Setting)

        self.assertEqual(s.instance, 'foo')
        self.assertEqual(s.attribute, 'bar')
        self.assertEqual(s.value, 0)

        content, _ = self.parser.parse_string(
            'configuration { foo.bar = !(true || false); }')

        self.assertLen(content.children, 1)
        conf = content.children[0]
        self.assertIsInstance(conf, Configuration)

        self.assertLen(conf.settings, 1)
        s = conf.settings[0]
        self.assertIsInstance(s, Setting)

        self.assertEqual(s.instance, 'foo')
        self.assertEqual(s.attribute, 'bar')
        self.assertEqual(s.value, 0)

    def test_boolean_literals_coercion(self):
        '''
        Test that boolean literals coerce to ints.
        '''
        content, _ = self.parser.parse_string(
            'configuration { foo.bar = (true + true) * (true + true) - false; }')

        self.assertLen(content.children, 1)
        conf = content.children[0]
        self.assertIsInstance(conf, Configuration)

        self.assertLen(conf.settings, 1)
        s = conf.settings[0]
        self.assertIsInstance(s, Setting)

        self.assertEqual(s.instance, 'foo')
        self.assertEqual(s.attribute, 'bar')
        self.assertEqual(s.value, 4)

        content, _ = self.parser.parse_string(
            'configuration { foo.bar = (true + 2) ** 3; }')

        self.assertLen(content.children, 1)
        conf = content.children[0]
        self.assertIsInstance(conf, Configuration)

        self.assertLen(conf.settings, 1)
        s = conf.settings[0]
        self.assertIsInstance(s, Setting)

        self.assertEqual(s.instance, 'foo')
        self.assertEqual(s.attribute, 'bar')
        self.assertEqual(s.value, 27)

    def test_negative_left_shift(self):
        '''
        Test constant folding of a left shift by a negative number. This should
        trigger an exception that CAmkES converts to a `ParseError`, but
        previously it did not. See CAMKES-440 for more information.
        '''
        with self.assertRaises(ParseError):
            self.parser.parse_string('configuration { foo.bar = 1 << -1; }')

    def test_negative_right_shift(self):
        '''
        Test constant folding of a right shift by a negative number. As above,
        this error should be converted.
        '''
        with self.assertRaises(ParseError):
            self.parser.parse_string('configuration { foo.bar = 1 >> -1; }')

    def test_overflow(self):
        '''
        Test constant folding of a calculation that deliberately induces an
        `OverflowError`.
        '''
        with self.assertRaises(MemoryError):
            self.parser.parse_string(
                'configuration { foo.bar = 1 << 2 ** 64; }')

    def test_basic_default_parameter_direction(self):
        '''
        A feature that was added late to CAmkES was the ability to omit the
        direction of a method parameter and have it assumed to be 'in'. This
        tests that such syntax is supported.
        '''
        content, _ = self.parser.parse_string('procedure P {\n'
                                              '  void foo(int x);\n'
                                              '}')

        self.assertLen(content.children, 1)
        P = content.children[0]
        self.assertIsInstance(P, Procedure)

        self.assertLen(P.methods, 1)
        foo = P.methods[0]

        self.assertLen(foo.parameters, 1)
        x = foo.parameters[0]

        self.assertEqual(x.direction, 'in')

    def test_complex_default_parameter_direction(self):
        '''
        Test a more complex example of default parameter directions.
        '''
        content, _ = self.parser.parse_string(
            'procedure P {\n'
            '  void foo(int x, inout unsigned int y, unsigned int z);\n'
            '  void bar(out int x, struct foo y, MyType_t z);\n'
            '}')

        self.assertLen(content.children, 1)
        P = content.children[0]
        self.assertIsInstance(P, Procedure)

        self.assertLen(P.methods, 2)
        foo, bar = P.methods

        self.assertLen(foo.parameters, 3)
        x, y, z = foo.parameters

        self.assertEqual(x.direction, 'in')
        self.assertEqual(x.type, 'int')

        self.assertEqual(y.direction, 'inout')
        self.assertEqual(y.type, 'unsigned int')

        self.assertEqual(z.direction, 'in')
        self.assertEqual(z.type, 'unsigned int')

        self.assertLen(bar.parameters, 3)
        x, y, z = bar.parameters

        self.assertEqual(x.direction, 'out')
        self.assertEqual(x.type, 'int')

        self.assertEqual(y.direction, 'in')
        self.assertEqual(y.type, 'struct foo')

        self.assertEqual(z.direction, 'in')
        self.assertEqual(z.type, 'MyType_t')

    def test_default_attributes(self):
        '''
        Test that we can set default values for attributes.
        '''
        content, _ = self.parser.parse_string(
            'component Foo {\n'
            '  attribute string x;\n'
            '  attribute string y = "hello world";\n'
            '  attribute int z = 42;\n'
            '}')

        self.assertLen(content.children, 1)
        Foo = content.children[0]
        self.assertIsInstance(Foo, Component)

        self.assertLen(Foo.attributes, 3)
        x, y, z = Foo.attributes

        self.assertIsNone(x.default)

        self.assertEqual(y.default, 'hello world')

        self.assertEqual(z.default, 42)

    def test_string_concat(self):
        '''
        Test that C-style string concatenation works.
        '''

        content, _ = self.parser.parse_string(
            'configuration {\n'
            '  foo.bar = "hello" "world";\n'
            '}')

        self.assertLen(content.children, 1)
        conf = content.children[0]
        self.assertIsInstance(conf, Configuration)

        self.assertLen(conf.settings, 1)
        foobar = conf.settings[0]
        self.assertIsInstance(foobar, Setting)

        self.assertEqual(foobar.instance, 'foo')
        self.assertEqual(foobar.attribute, 'bar')

        self.assertEqual(foobar.value, 'helloworld')

    def test_string_concat_line_split(self):
        '''
        Test that C-style string concatenation works across line breaks.
        '''

        content, _ = self.parser.parse_string(
            'configuration {\n'
            '  foo.bar = "hello" \n'
            '"world";\n'
            '}')

        self.assertLen(content.children, 1)
        conf = content.children[0]
        self.assertIsInstance(conf, Configuration)

        self.assertLen(conf.settings, 1)
        foobar = conf.settings[0]
        self.assertIsInstance(foobar, Setting)

        self.assertEqual(foobar.instance, 'foo')
        self.assertEqual(foobar.attribute, 'bar')

        self.assertEqual(foobar.value, 'helloworld')

    def test_loose_semicolons(self):
        '''
        Test that we can cope with empty statements.
        '''
        content, _ = self.parser.parse_string(';;;')
        self.assertLen(content.children, 0)

    def test_c_include(self):
        '''
        Test we can parse a relative C include.
        '''
        content, _ = self.parser.parse_string(
            'procedure P { include "hello.h"; }')

        self.assertLen(content.children, 1)
        P = content.children[0]
        self.assertIsInstance(P, Procedure)

        self.assertLen(P.children, 1)
        include = P.children[0]
        self.assertIsInstance(include, Include)

        self.assertTrue(include.relative)
        self.assertEqual(include.source, 'hello.h')

    def test_c_include2(self):
        '''
        Test we can parse a relative C include that relies on multi strings.
        '''
        content, _ = self.parser.parse_string(
            'procedure P { include "hello" "world"; }')

        self.assertLen(content.children, 1)
        P = content.children[0]
        self.assertIsInstance(P, Procedure)

        self.assertLen(P.children, 1)
        include = P.children[0]
        self.assertIsInstance(include, Include)

        self.assertTrue(include.relative)
        self.assertEqual(include.source, 'helloworld')


if __name__ == '__main__':
    unittest.main()
