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
from camkes.parser.exception import ParseError

class TestStage1(CAmkESTest):
    def setUp(self):
        super(TestStage1, self).setUp()
        r = Reader()
        self.parser = Parse1(r)

        r = CPP()
        self.cpp_parser = Parse1(r)

    def test_empty_string(self):
        source, content, read = self.parser.parse_string('')

        self.assertEqual(source, '')
        self.assertEqual(content.head, 'start')
        self.assertEqual(content.tail, [])
        self.assertLen(read, 0)

    def test_basic_entity(self):
        source, content, read = self.parser.parse_string('component foo {}')

        self.assertEqual(source, 'component foo {}')
        self.assertEqual(content.head, 'start')
        self.assertLen(content.tail, 1)
        self.assertEqual(content.tail[0].head, 'component_decl')
        self.assertLen(content.tail[0].tail, 2)
        self.assertEqual(content.tail[0].tail[0].head, 'id')
        self.assertLen(content.tail[0].tail[0].tail, 1)
        self.assertEqual(content.tail[0].tail[0].tail[0], 'foo')
        self.assertEqual(content.tail[0].tail[1].head, 'component_defn')
        self.assertLen(content.tail[0].tail[1].tail, 0)
        self.assertLen(read, 0)

    def test_numerics_basic(self):
        source, content, read = self.parser.parse_string(
            'configuration { hello.world = 1 + 4 - 2; }')

        self.assertEqual(source,
            'configuration { hello.world = 1 + 4 - 2; }')
        self.assertEqual(content.head, 'start')
        self.assertLen(content.tail, 1)
        self.assertEqual(content.tail[0].head, 'configuration_decl')

        self.assertLen(content.tail[0].tail, 1)
        self.assertEqual(content.tail[0].tail[0].head, 'configuration_defn')
        configuration_defn = content.tail[0].tail[0]

        self.assertLen(configuration_defn.tail, 1)
        self.assertEqual(configuration_defn.tail[0].head, 'setting')
        setting = configuration_defn.tail[0]

        self.assertLen(setting.tail, 3)
        self.assertEqual(setting.tail[0].head, 'id')
        self.assertLen(setting.tail[0].tail, 1)
        self.assertEqual(setting.tail[0].tail[0], 'hello')
        self.assertEqual(setting.tail[1].head, 'id')
        self.assertLen(setting.tail[1].tail, 1)
        self.assertEqual(setting.tail[1].tail[0], 'world')
        p = setting.tail[2]

        self.assertEqual(p.head, 'precedence11')
        self.assertLen(p.tail, 1)
        p = p.tail[0]

        self.assertEqual(p.head, 'precedence10')
        self.assertLen(p.tail, 1)
        p = p.tail[0]

        self.assertEqual(p.head, 'precedence9')
        self.assertLen(p.tail, 1)
        p = p.tail[0]

        self.assertEqual(p.head, 'precedence8')
        self.assertLen(p.tail, 1)
        p = p.tail[0]

        self.assertEqual(p.head, 'precedence7')
        self.assertLen(p.tail, 1)
        p = p.tail[0]

        self.assertEqual(p.head, 'precedence6')
        self.assertLen(p.tail, 1)
        p = p.tail[0]

        self.assertEqual(p.head, 'precedence5')
        self.assertLen(p.tail, 1)
        p = p.tail[0]

        self.assertEqual(p.head, 'precedence4')
        self.assertLen(p.tail, 1)
        p = p.tail[0]

        self.assertEqual(p.head, 'precedence3')
        self.assertLen(p.tail, 1)
        p = p.tail[0]

        self.assertEqual(p.head, 'precedence2')
        self.assertLen(p.tail, 5)

        self.assertEqual(p.tail[0].head, 'precedence1')
        self.assertLen(p.tail[0].tail, 1)
        self.assertEqual(p.tail[0].tail[0].head, 'number')
        self.assertLen(p.tail[0].tail[0].tail, 1)
        self.assertEqual(p.tail[0].tail[0].tail[0], '1')

        self.assertEqual(p.tail[1].head, 'add')

        self.assertEqual(p.tail[2].head, 'precedence1')
        self.assertLen(p.tail[2].tail, 1)
        self.assertEqual(p.tail[2].tail[0].head, 'number')
        self.assertLen(p.tail[0].tail[0].tail, 1)
        self.assertEqual(p.tail[2].tail[0].tail[0], '4')

        self.assertEqual(p.tail[3].head, 'sub')

        self.assertEqual(p.tail[4].head, 'precedence1')
        self.assertLen(p.tail[4].tail, 1)
        self.assertEqual(p.tail[4].tail[0].head, 'number')
        self.assertLen(p.tail[4].tail[0].tail, 1)
        self.assertEqual(p.tail[4].tail[0].tail[0], '2')

    def test_numerics_precedence(self):
        source, content, read = self.parser.parse_string(
            'configuration { hello.world = 1 + 4 * 2; }')

        self.assertEqual(source,
            'configuration { hello.world = 1 + 4 * 2; }')

        self.assertEqual(content.head, 'start')
        self.assertLen(content.tail, 1)
        self.assertEqual(content.tail[0].head, 'configuration_decl')

        self.assertLen(content.tail[0].tail, 1)
        self.assertEqual(content.tail[0].tail[0].head, 'configuration_defn')
        configuration_defn = content.tail[0].tail[0]

        self.assertLen(configuration_defn.tail, 1)
        self.assertEqual(configuration_defn.tail[0].head, 'setting')
        setting = configuration_defn.tail[0]

        self.assertLen(setting.tail, 3)
        self.assertEqual(setting.tail[0].head, 'id')
        self.assertLen(setting.tail[0].tail, 1)
        self.assertEqual(setting.tail[0].tail[0], 'hello')
        self.assertEqual(setting.tail[1].head, 'id')
        self.assertLen(setting.tail[1].tail, 1)
        self.assertEqual(setting.tail[1].tail[0], 'world')
        p = setting.tail[2]

        self.assertEqual(p.head, 'precedence11')
        self.assertLen(p.tail, 1)
        p = p.tail[0]

        self.assertEqual(p.head, 'precedence10')
        self.assertLen(p.tail, 1)
        p = p.tail[0]

        self.assertEqual(p.head, 'precedence9')
        self.assertLen(p.tail, 1)
        p = p.tail[0]

        self.assertEqual(p.head, 'precedence8')
        self.assertLen(p.tail, 1)
        p = p.tail[0]

        self.assertEqual(p.head, 'precedence7')
        self.assertLen(p.tail, 1)
        p = p.tail[0]

        self.assertEqual(p.head, 'precedence6')
        self.assertLen(p.tail, 1)
        p = p.tail[0]

        self.assertEqual(p.head, 'precedence5')
        self.assertLen(p.tail, 1)
        p = p.tail[0]

        self.assertEqual(p.head, 'precedence4')
        self.assertLen(p.tail, 1)
        p = p.tail[0]

        self.assertEqual(p.head, 'precedence3')
        self.assertLen(p.tail, 1)
        p = p.tail[0]

        self.assertEqual(p.head, 'precedence2')
        self.assertLen(p.tail, 3)

        self.assertEqual(p.tail[0].head, 'precedence1')
        self.assertLen(p.tail[0].tail, 1)
        self.assertEqual(p.tail[0].tail[0].head, 'number')
        self.assertLen(p.tail[0].tail[0].tail, 1)
        self.assertEqual(p.tail[0].tail[0].tail[0], '1')

        self.assertEqual(p.tail[1].head, 'add')

        self.assertEqual(p.tail[2].head, 'precedence1')
        self.assertLen(p.tail[2].tail, 3)
        self.assertEqual(p.tail[2].tail[0].head, 'number')
        self.assertLen(p.tail[0].tail[0].tail, 1)
        self.assertEqual(p.tail[2].tail[0].tail[0], '4')

        self.assertEqual(p.tail[2].tail[1].head, 'mul')

        self.assertEqual(p.tail[2].tail[2].head, 'number')
        self.assertLen(p.tail[2].tail[2].tail, 1)
        self.assertEqual(p.tail[2].tail[2].tail[0], '2')

    def test_malformed(self):
        with self.assertRaises(Exception):
            self.parser.parse_string('hello world')

    def test_unicode(self):
        source, content, read = self.parser.parse_string('component foó {}')

        self.assertEqual(source, 'component foó {}')
        self.assertEqual(content.head, 'start')
        self.assertLen(content.tail, 1)
        self.assertEqual(content.tail[0].head, 'component_decl')
        self.assertLen(content.tail[0].tail, 2)
        self.assertEqual(content.tail[0].tail[0].head, 'id')
        self.assertLen(content.tail[0].tail[0].tail, 1)
        self.assertEqual(content.tail[0].tail[0].tail[0], 'foó')
        self.assertEqual(content.tail[0].tail[1].head, 'component_defn')
        self.assertLen(content.tail[0].tail[1].tail, 0)
        self.assertLen(read, 0)

    def test_from_file(self):
        tmp = self.mkstemp()
        with open(tmp, 'wt') as f:
            f.write('component foo {}')

        source, content, read = self.parser.parse_file(tmp)

        self.assertEqual(source, 'component foo {}')
        self.assertEqual(content.head, 'start')
        self.assertLen(content.tail, 1)
        self.assertEqual(content.tail[0].head, 'component_decl')
        self.assertLen(content.tail[0].tail, 2)
        self.assertEqual(content.tail[0].tail[0].head, 'id')
        self.assertLen(content.tail[0].tail[0].tail, 1)
        self.assertEqual(content.tail[0].tail[0].tail[0], 'foo')
        self.assertEqual(content.tail[0].tail[1].head, 'component_defn')
        self.assertLen(content.tail[0].tail[1].tail, 0)
        self.assertEqual(read, set([tmp]))

    @unittest.skipIf(not cpp_available(), 'CPP not found')
    def test_with_cpp(self):
        parent = self.mkstemp()
        child = self.mkstemp()

        with open(parent, 'wt') as f:
            f.write('component foo\n#include "%s"' % child)
        with open(child, 'wt') as f:
            f.write('{}')

        _, content, read = self.cpp_parser.parse_file(parent)

        self.assertEqual(content.head, 'start')
        self.assertLen(content.tail, 1)
        self.assertEqual(content.tail[0].head, 'component_decl')
        self.assertLen(content.tail[0].tail, 2)
        self.assertEqual(content.tail[0].tail[0].head, 'id')
        self.assertLen(content.tail[0].tail[0].tail, 1)
        self.assertEqual(content.tail[0].tail[0].tail[0], 'foo')
        self.assertEqual(content.tail[0].tail[1].head, 'component_defn')
        self.assertLen(content.tail[0].tail[1].tail, 0)

        self.assertIn(parent, read)
        self.assertIn(child, read)

    def test_lineno_basic(self):
        _, content, _ = self.parser.parse_string('component foo {}')

        self.assertEqual(content.head, 'start')
        self.assertLen(content.tail, 1)
        self.assertEqual(content.tail[0].head, 'component_decl')
        component_decl = content.tail[0]

        component_decl.calc_position()
        self.assertEqual(component_decl.min_line, 1)

    def test_lineno_basic2(self):
        _, content, _ = self.parser.parse_string('\ncomponent foo {}')

        self.assertEqual(content.head, 'start')
        self.assertLen(content.tail, 1)
        self.assertEqual(content.tail[0].head, 'component_decl')
        component_decl = content.tail[0]

        component_decl.calc_position()
        self.assertEqual(component_decl.min_line, 2)

    def test_lineno_basic3(self):
        _, content, _ = self.parser.parse_string('component\nfoo\n{\n}')

        self.assertEqual(content.head, 'start')
        self.assertLen(content.tail, 1)
        self.assertEqual(content.tail[0].head, 'component_decl')
        component_decl = content.tail[0]

        component_decl.calc_position()
        self.assertIn(component_decl.min_line, (1, 2))

    def test_lineno_comment(self):
        _, content, _ = self.parser.parse_string('//I\'m a comment\ncomponent foo {}')

        self.assertEqual(content.head, 'start')
        self.assertLen(content.tail, 1)
        self.assertEqual(content.tail[0].head, 'component_decl')
        component_decl = content.tail[0]

        component_decl.calc_position()
        self.assertEqual(component_decl.min_line, 2)

    def test_lineno_comment2(self):
        _, content, _ = self.parser.parse_string('/* I\'m a comment */\ncomponent foo {}')

        self.assertEqual(content.head, 'start')
        self.assertLen(content.tail, 1)
        self.assertEqual(content.tail[0].head, 'component_decl')
        component_decl = content.tail[0]

        component_decl.calc_position()
        self.assertEqual(component_decl.min_line, 2)

    def test_lineno_multiline_comment(self):
        _, content, _ = self.parser.parse_string('/*I\'m a \nmultiline comment*/\ncomponent foo {}')

        self.assertEqual(content.head, 'start')
        self.assertLen(content.tail, 1)
        self.assertEqual(content.tail[0].head, 'component_decl')
        component_decl = content.tail[0]

        component_decl.calc_position()
        self.assertEqual(component_decl.min_line, 3)

    def test_lineno_multiline_comment2(self):
        _, content, _ = self.parser.parse_string('/*I\'m\na\nmultiline\ncomment*/\ncomponent foo {}')

        self.assertEqual(content.head, 'start')
        self.assertLen(content.tail, 1)
        self.assertEqual(content.tail[0].head, 'component_decl')
        component_decl = content.tail[0]

        component_decl.calc_position()
        self.assertEqual(component_decl.min_line, 5)

    def test_simple_spec_complete(self):
        _, content, _ = self.parser.parse_string('''
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

    def test_multiline_comment_preserves_line_numbers(self):
        _, content, _ = self.parser.parse_string('''
            /* multiline comment
             * that may affect line numbering
             * if we've messed up
             */
            procedure P {}
            ''')

        self.assertEqual(content.head, 'start')
        self.assertLen(content.tail, 1)
        P = content.tail[0]
        self.assertEqual(P.head, 'procedure_decl')

        P.calc_position()
        self.assertEqual(P.min_line, 6)

    def test_manual_line_directives(self):
        '''
        GCC supports two forms of line directive:

            #line <linenum> <filename>

            # <linenum> <filename>

        Only the first of these is documented in [0], though it is actually the
        second of these that the C pre processor outputs. CAmkES' understanding
        of these directives was previously based on observed directives from
        CPP and it could not understand the first of these. This test checks
        that it can now understand the first of these as well, as these may be
        in use by some other non-CPP pre processing tool.

          [0]: https://gcc.gnu.org/onlinedocs/cpp/Line-Control.html
        '''

        # Deliberately parse a malformed spec to generate an error.
        try:
            self.parser.parse_string('''

                #line 42 "A"

                connector Foo {
                    from Procedure bar;
                    to Procedure baz;
                }
                ''')

            # If we reached this point, the malformed spec did not trigger an
            # error as expected.
            self.fail('incorrect syntax accepted by stage 1 parser')

        except ParseError as e:
            error = e

        self.assertRegexpMatches(str(error), 'A:44:', 'alternate form of line '
            'directive not supported')

    def test_multiple_error_message_line_numbers(self):
        '''
        This test checks that when multiple PlyPlus errors are triggered on a
        spec that has C pre-processor line directives, the correct source line
        is still located in the error message. There was previously an issue
        where line number information would not be provided in this case.
        '''

        # Parse a malformed spec with some line directives. Note that the spec
        # contains the old form of connector definition.
        try:
            self.parser.parse_string('''

                # 42 "A"

                connector Foo {
                    from Procedure bar;
                    to Procedure baz;
                }

                connector Qux {
                    from Procedure Moo;
                    from Procedure Cow;
                }
                ''')

            # If we reached this point, the malformed spec did not trigger an
            # error as expected.
            self.fail('incorrect syntax accepted by stage 1 parser')

        except ParseError as e:
            self.assertGreaterEqual(len(e.args), 2, 'only a '
                'single error triggered when multiple were expected')

            # If the line number narrowing algorithm has correctly taken the
            # line directive into account, we should get the following prefix.
            self.assertRegexpMatches(str(e), 'A:44:', 'line directive not '
                'accounted for')

    def test_list_dict_key(self):
        '''
        Test using a list as a key in a dictionary used as a setting. Should
        not be accepted.
        '''
        with self.assertRaises(ParseError):
            self.parser.parse_string(
                'configuration {\n'
                '  foo.bar = {[1, 2, 3]: 3};\n'
                '}')

    def test_c_include(self):
        '''
        Test we can parse a C relative path include.
        '''
        _, content, _ = self.parser.parse_string(
            'procedure Foo { include "hello.h"; }')

        self.assertEqual(content.head, 'start')
        self.assertLen(content.tail, 1)

        self.assertEqual(content.tail[0].head, 'procedure_decl')
        proc_decl = content.tail[0]

        self.assertLen(proc_decl.tail, 2)
        self.assertEqual(proc_decl.tail[0].head, 'id')
        self.assertLen(proc_decl.tail[0].tail, 1)
        self.assertEqual(proc_decl.tail[0].tail[0], 'Foo')

        self.assertEqual(proc_decl.tail[1].head, 'procedure_defn')
        proc_defn = proc_decl.tail[1]

        self.assertLen(proc_defn.tail, 1)
        self.assertEqual(proc_defn.tail[0].head, 'include')
        include = proc_defn.tail[0]

        self.assertLen(include.tail, 1)
        self.assertEqual(include.tail[0].head, 'multi_string')
        multi_string = include.tail[0]

        self.assertLen(multi_string.tail, 1)
        self.assertEqual(multi_string.tail[0].head, 'quoted_string')
        quoted_string = multi_string.tail[0]

        self.assertLen(quoted_string.tail, 1)
        self.assertEqual(quoted_string.tail[0], '"hello.h"')

if __name__ == '__main__':
    unittest.main()
