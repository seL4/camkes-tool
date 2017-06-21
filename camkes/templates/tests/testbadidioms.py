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
Tests that look for incorrect Python idioms in the templates.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals

import os, re, subprocess, sys, unittest

ME = os.path.abspath(__file__)

# Make CAmkES importable
sys.path.append(os.path.join(os.path.dirname(ME), '../../..'))

from camkes.internal.tests.utils import CAmkESTest

class TestBadIdioms(CAmkESTest):
    pass

def _string_addition(self, path):
    '''
    Look for string addition instead of using format strings.
    '''
    regex = re.compile(r'(\'.*?\'\s*\+|\+\s*\'.*?\')')
    with open(path, 'rt') as f:
        for lineno, line in enumerate(f, 1):
            if regex.search(line) is not None:
                self.fail('%s:%d: %s\nstring addition instead of format string?'
                    % (path, lineno, line))

regex = re.compile(r'[^\w]')
template_dir = os.path.abspath(os.path.join(os.path.dirname(ME), '..'))
tests_dir = os.path.dirname(ME)

# Find all the templates.
for root, _, filenames in os.walk(template_dir):

    if root.startswith(tests_dir):
        # Don't analyse the test files.
        continue

    # For each template, monkey patch a test for it onto the test class.
    for f in filenames:
        if f.endswith('.swp') or f.endswith('.py'):
            # Skip vim lock files.
            continue
        name = 'test_%s' % regex.sub('_', f)
        path = os.path.join(root, f)
        setattr(TestBadIdioms, name, lambda self, path=path: _string_addition(self, path))

if __name__ == '__main__':
    unittest.main()
