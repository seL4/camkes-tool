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

from camkes.internal.tests.utils import CAmkESTest
from camkes.ast import ASTError
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

class TestStage9(CAmkESTest):
    def setUp(self):
        super(TestStage9, self).setUp()
        r = Reader()
        s1 = Parse1(r)
        s2 = Parse2(s1)
        s3 = Parse3(s2, debug=True)
        s4 = Parse4(s3)
        s5 = Parse5(s4)
        s6 = Parse6(s5)
        s7 = Parse7(s6)
        s8 = Parse8(s7)
        self.parser = Parse9(s8)

    def test_invalid_repeated_interfaces_before(self):
        ''' Introduces an invalid N-1 connection BEFORE a valid connection '''
        with six.assertRaisesRegex(self, ParseError, 'Multiple connections involving'):
            self.parser.parse_string('''
            connector C {
                from Dataport;
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
                    connection C c2(from b.p2, to f.p1, to f.p2);
                    connection C c1(from b.p1, to f.p1);
                }
            }
            ''')

    def test_invalid_repeated_interfaces_after(self):
        ''' Introduces an invalid N-1 connection AFTER a valid connection '''
        with six.assertRaisesRegex(self, ParseError, 'Multiple connections involving'):
            self.parser.parse_string('''
            connector C {
                from Dataport;
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
                    connection C c2(from b.p2, to f.p1, to f.p2);
                }
            }
            ''')

    def test_both_sides(self):
        with six.assertRaisesRegex(self, ParseError, 'Interface f.p1 appears on to and from side'):
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

    def test_repeated_connection(self):
        with six.assertRaisesRegex(self, ParseError, 'Multiple connections between interfaces'):
            self.parser.parse_string('''
            connector C {
                from Dataports;
                to Dataports;
            }
            component Foo {
                dataport Buf p1;
            }
            component Baz {
                dataport Buf p1;
            }
            assembly {
                composition {
                    component Foo f;
                    component Baz b;
                    connection C c1(from b.p1, to f.p1);
                    connection C c2(from b.p1, to f.p1);
                }
            }
            ''')

    def test_multiple_connectors(self):
        with six.assertRaisesRegex(self, ParseError, 'Multiple connectors used in connections'):
            self.parser.parse_string('''
            connector C1 {
                from Dataports;
                to Dataports;
            }
            connector C2 {
                from Dataports;
                to Dataports;
            }
            component Foo {
                dataport Buf p1;
            }
            component Baz {
                dataport Buf p1;
                dataport Buf p2;
            }
            assembly {
                composition {
                    component Foo f;
                    component Baz b;
                    connection C1 c1(from b.p1, to f.p1);
                    connection C2 c2(from b.p2, to f.p1);
                }
            }
            ''')

if __name__ == '__main__':
    unittest.main()
