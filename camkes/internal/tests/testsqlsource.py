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

'''
Tests that the external SQL sources used by the level A cache are syntactically
correct.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals

import os, re, sys, unittest

ME = os.path.abspath(__file__)

# Make CAmkES importable
sys.path.append(os.path.join(os.path.dirname(ME), '../../..'))

from camkes.internal.tests.utils import c_compiler, CAmkESTest

class TestSQLSource(CAmkESTest):
    def setUp(self):
        super(TestSQLSource, self).setUp()
        sqlite_lint_c = os.path.abspath(os.path.join(os.path.dirname(ME),
            '../../../tools/sqlite-lint.c'))
        tmp = self.mkdtemp()

        self.sqlite_lint = os.path.join(tmp, 'sqlite-lint')

        cc = c_compiler()
        self.assertIsNotNone(cc, 'no C compiler available')

        ret, _, stderr = self.execute([cc, '-W', '-Wall', '-Wextra', '-Werror',
            '-o', self.sqlite_lint, sqlite_lint_c, '-lsqlite3'])
        self.assertEqual(ret, 0, 'failed to build sqlite-lint.c:\n%s' % stderr)

    def _sqlite_lint(self, path):
        assert self.sqlite_lint is not None
        ret, _, stderr = self.execute([self.sqlite_lint, path])
        self.assertEqual(ret, 0, stderr)

# Find all SQL sources in our parent directory and monkey patch test cases for
# them onto the test class.
d = os.path.join(os.path.dirname(ME), '..')
for f in os.listdir(d):
    if not f.lower().endswith('.sql'):
        continue
    path = os.path.abspath(os.path.join(d, f))
    name = 'test_%s' % re.sub(r'[^\w]', '_', f)
    setattr(TestSQLSource, name,
        lambda self, path=path: self._sqlite_lint(path))

if __name__ == '__main__':
    unittest.main()
