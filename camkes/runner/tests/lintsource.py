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

import os, re, sys, unittest
from pylint import epylint

ME = os.path.abspath(__file__)

# Make CAmkES importable
sys.path.append(os.path.join(os.path.dirname(ME), '../../..'))

from camkes.internal.tests.utils import CAmkESTest

CAMKES_LINT = os.path.join(os.path.dirname(ME),
    '../../../tools/camkes_lint.py')

class TestSourceLint(CAmkESTest):
    pass

def lint(self, path):
    ret, _, stderr = self.execute([CAMKES_LINT, path])
    self.assertEqual(ret, 0, stderr)

srcdir = os.path.join(os.path.dirname(ME), '..')
regex = re.compile(r'.*\.py$')
sub = re.compile(r'[^\w]')
for src in os.listdir(srcdir):
    if regex.match(src) is None:
        continue
    path = os.path.abspath(os.path.join(srcdir, src))
    name = 'test_%s' % sub.sub('_', src)
    setattr(TestSourceLint, name, lambda self, path=path: lint(self, path))

if __name__ == '__main__':
    unittest.main()
