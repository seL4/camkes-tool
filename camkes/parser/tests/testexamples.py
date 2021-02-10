#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#
#

'''
Tests for input from good/ subdirectory, that are intended to be legitimate
CAmkES input.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals

import functools, os, re, sys, unittest

ME = os.path.abspath(__file__)

# Make CAmkES importable
sys.path.append(os.path.join(os.path.dirname(ME), '../../..'))

from camkes.ast import ASTError
from camkes.internal.tests.utils import CAmkESTest, cpp_available
from camkes.parser import ParseError
from camkes.parser.stage0 import CPP, Reader
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
from camkes.parser.query import QueryParseStage
from camkes.parser.fdtQueryEngine import DtbMatchQuery

PARSERS = ('reader', 'cpp', 's1', 's2', 's3', 's4', 's5', 's6', 's7', 's71', 's8', 's9', 's10')

class TestExamples(CAmkESTest):
    def setUp(self):
        super(TestExamples, self).setUp()
        self.reader = Reader()
        self.cpp = CPP()
        self.s1 = Parse1(self.cpp)
        self.s2 = Parse2(self.s1)
        self.s3 = Parse3(self.s2)
        self.s4 = Parse4(self.s3)
        self.s5 = Parse5(self.s4)
        self.s6 = Parse6(self.s5)
        self.s7 = Parse7(self.s6)

        # initialise a dtb query parser
        dtbQuery = DtbMatchQuery()
        dtbQuery.parse_args(['--dtb', os.path.join(os.path.dirname(ME), "test.dtb")])
        dtbQuery.check_options()

        self.s71 = QueryParseStage(self.s7, {dtbQuery.get_query_name() : dtbQuery})
        self.s8 = Parse8(self.s71)
        self.s9 = Parse9(self.s8)
        self.s10 = Parse10(self.s9)
        assert all([hasattr(self, p) for p in PARSERS])

# Locate all the test files in good/*.camkes and add each as a separate test
# case for each parser.
added_good = False
for eg in os.listdir(os.path.join(os.path.dirname(ME), 'good')):
    if re.match(r'.*\.camkes$', eg) is not None:
        path = os.path.join(os.path.dirname(ME), 'good', eg)
        for parser in PARSERS:
            test_name = 'test_good_%s_%s' % (parser, re.sub(r'[^\w]', '_', eg))
            setattr(TestExamples, test_name,
                lambda self, f=path, p=parser: getattr(self, p).parse_file(f))
        added_good = True
if not added_good:
    # We didn't find any valid tests.
    def no_good(self):
        self.fail('no good example input found')
    TestExamples.test_no_good = no_good

def _check_until(tester, filename, limit):
    for p in PARSERS:
        if p == limit:
            with tester.assertRaises((ASTError, ParseError)):
                getattr(tester, p).parse_file(filename)
            break
        else:
            getattr(tester, p).parse_file(filename)

# Locate all the files in bad-at-*/*.camkes and add each as a separate test
# case, failing at the specific parser level.
for p in PARSERS:
    dirname = os.path.join(os.path.dirname(ME), 'bad-at-%s' % p)
    if not os.path.exists(dirname):
        continue
    for eg in os.listdir(dirname):
        if re.match(r'.*\.camkes$', eg) is not None:
            path = os.path.join(dirname, eg)
            test_name = 'test_bad_at_%s_%s' % (p, re.sub(r'[^\w]', '_', eg))
            setattr(TestExamples, test_name,
                lambda self, f=path, limit=p: _check_until(self, f, limit))

if __name__ == '__main__':
    unittest.main()
