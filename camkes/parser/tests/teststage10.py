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

from camkes.ast import ASTError
from camkes.internal.tests.utils import CAmkESTest
from camkes.parser import ParseError
from camkes.parser.stage0 import Reader
from camkes.parser.stage1 import Parse1
from camkes.parser.stage2 import Parse2
from camkes.parser.stage3 import Parse3
from camkes.parser.stage4 import Parse4
from camkes.parser.stage5 import Parse5
from camkes.parser.stage6 import Parse6
from camkes.parser.stage7 import Parse7
from camkes.parser.stage8 import Parse8
from camkes.parser.stage9 import Parse9
from camkes.parser.stage10 import Parse10

class TestStage10(CAmkESTest):
    def setUp(self):
        super(TestStage10, self).setUp()
        r = Reader()
        s1 = Parse1(r)
        s2 = Parse2(s1)
        s3 = Parse3(s2, debug=True)
        s4 = Parse4(s3)
        s5 = Parse5(s4)
        s6 = Parse6(s5)
        s7 = Parse7(s6)
        s8 = Parse8(s7)
        s9 = Parse9(s8)
        self.parser = Parse10(s9)

    def test_basic_assignment(self):
        ast, _ = self.parser.parse_string('''
            connector C {
                from Procedure;
                to Procedure;
            }
            procedure P {
            }
            component Foo {
                attribute string t;
                provides P p;
            }
            component Baz {
                uses P p;
            }
            assembly {
                composition {
                    component Foo f;
                    component Baz b;
                    connection C c(from b.p, to f.p);
                }
                configuration {
                    f.t = "hello world";
                }
            }
            ''')

        self.assertLen(ast.items, 5)
        C, P, Foo, Baz, assembly = ast.items

        self.assertLen(assembly.configuration.settings, 1)
        s = assembly.configuration.settings[0]

        self.assertEqual(s.value, 'hello world')

    def test_mistyped_assignment(self):
        with self.assertRaises((ASTError, ParseError)):
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
                component Baz {
                    uses P p;
                }
                assembly {
                    composition {
                        component Foo f;
                        component Baz b;
                        connection C c(from b.p, to f.p);
                    }
                    configuration {
                        f.t = 2;
                    }
                }
                ''')

    def test_mistyped_hierarchical_assignment(self):
        with self.assertRaises((ASTError, ParseError)):
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
                        b1.s = 2;
                    }
                }
                ''')

    def test_mistyped_attribute(self):
        with self.assertRaises((ASTError, ParseError)):
            ast, _ = self.parser.parse_string('''
                connector C {
                    from Procedure;
                    to Procedure;
                }
                procedure P {
                }
                component Foo {
                    attribute int t;
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

    def test_setting_duplication_bug(self):
        '''
        There was a bug in an early implementation of the parser that led to
        settings in non-trivial hierarchical specs being potentially duplicated
        as they were lifted up the AST. This tests whether such a bug has been
        re-introduced. If it has, this test should throw a ParseError with a
        message about duplicate settings of the attribute string_to_append.
        '''
        spec = '''
/* This spec lifted from the hierarchical components example at time of
 * writing.
 */
connector seL4RPC {
    from Procedure;
    to Procedure;
}
procedure StringProcessor {
    void process(in string input);
};
component Client {
    control;
    uses StringProcessor o1;
    uses StringProcessor o2;
}
component Server {
    provides StringProcessor i;
}
component UpperCase {
    provides StringProcessor i;
    uses StringProcessor o;
}
component Reverse {
    provides StringProcessor i;
    uses StringProcessor o;
}
component Append {

    provides StringProcessor i;
    uses StringProcessor o;

    attribute string string_to_append;
}
component SubPipeline {
    provides StringProcessor i;
    uses StringProcessor o;

    composition {

        component UpperCase uc;
        component Reverse r;

        connection seL4RPC internal(from uc.o, to r.i);

        export r.o -> o;
        export uc.i -> i;
    }
}
component Pipeline {
    provides StringProcessor i;
    uses StringProcessor o;

    provides StringProcessor extra;

    composition {

        component SubPipeline sp;
        component Append a;

        connection seL4RPC internal1(from a.o, to sp.i);

        export sp.o -> o;
        export a.i -> i;
    }
    configuration {
        a.string_to_append = "world";
    }
}
assembly {
    composition {
        component Client c;
        component Server s;

        component Pipeline p1;
        component Pipeline p2;

        connection seL4RPC client_external(from c.o1, to p1.i);
        connection seL4RPC pipeline_connection(from p1.o, to p2.i);
        connection seL4RPC server_external(from p2.o, to s.i);
        connection seL4RPC extra_external(from c.o2, to p1.extra);
    }
}
'''

        self.parser.parse_string(spec)

    def test_attribute_default_values_in_settings(self):
        '''
        Test that an attribute without its value set has its default value
        accessible through the configuration settings.
        '''
        spec = '''
            connector C {
                from Procedures;
                to Procedure;
            }
            procedure P {}
            component Foo {
                attribute string x = "hello world";
                attribute int y;
                uses P p;
            }
            component Bar {
                provides P p;
            }
            assembly {
                composition {
                    component Foo f1;
                    component Foo f2;
                    component Bar b;
                    connection C conn1(from f1.p, from f2.p, to b.p);
                }
                configuration {
                    f1.x = "moo cow";
                    f1.y = 1;
                    f2.y = 2;
                }
            }
        '''

        ast, _ = self.parser.parse_string(spec)

        conf = ast.assembly.configuration

        self.assertIn('f1', conf)
        self.assertIn('x', conf['f1'])
        self.assertEqual(conf['f1']['x'], 'moo cow')

        self.assertIn('y', conf['f1'])
        self.assertEqual(conf['f1']['y'], 1)

        self.assertIn('f2', conf)
        self.assertIn('x', conf['f2'])
        self.assertEqual(conf['f2']['x'], 'hello world')

        self.assertIn('y', conf['f2'])
        self.assertEqual(conf['f2']['y'], 2)

    def test_attribute_c_keyword(self):
        '''
        Confirm that we can't use an attribute name that is a C keyword.
        '''
        spec = '''
            connector C {
                from Procedure;
                to Procedure;
            }
            procedure P {
            }
            component Foo {
                attribute string for;
                provides P p;
            }
            component Baz {
                uses P p;
            }
            assembly {
                composition {
                    component Foo f;
                    component Baz b;
                    connection C c(from b.p, to f.p);
                }
            }
            '''

        with self.assertRaises(ASTError):
            self.parser.parse_string(spec)

    def test_setting_c_keyword(self):
        '''
        Confirm that we can't set an undeclared attribute with the name of a C
        keyword.
        '''
        spec = '''
            connector C {
                from Procedure;
                to Procedure;
            }
            procedure P {
            }
            component Foo {
                provides P p;
            }
            component Baz {
                uses P p;
            }
            assembly {
                composition {
                    component Foo f;
                    component Baz b;
                    connection C c(from b.p, to f.p);
                }
                configuration {
                    f.for = "hello world";
                }
            }
            '''

        with self.assertRaises(ASTError):
            self.parser.parse_string(spec)

    def test_both_sides(self):
        with six.assertRaisesRegex(self, ASTError, r'.*duplicate use of interface f.p1 \(deprecated form of N-way connections\?\)'):
            self.parser.parse_string('''
            connector C {
                from Dataports;
                to Dataports;
            }
            component Foo {
                dataport Buf p1;
                dataport Buf p2;
            }
            component Baz {
                dataport Buf p1;
                dataport Buf p2;
            }
            assembly {
                composition {
                    component Foo f;
                    component Baz b;
                    connection C c1(from b.p1, to f.p1);
                    connection C c2(from f.p1, to b.p2);
                }
            }
            ''')


if __name__ == '__main__':
    unittest.main()
