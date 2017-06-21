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
Test harness for running jinja_pylint.py across the templates.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals

import os, re, subprocess, sys, unittest

ME = os.path.abspath(__file__)

# Make CAmkES importable
sys.path.append(os.path.join(os.path.dirname(ME), '../../..'))

from camkes.internal.tests.utils import CAmkESTest

class TestPyLint(CAmkESTest):
    def setUp(self):
        super(TestPyLint, self).setUp()
        self.lint = os.path.join(os.path.dirname(ME),
            '../../../tools/jinja_pylint.py')
        self.assertTrue(os.access(self.lint, os.X_OK),
            'jinja_pylint.py not found or not executable')

# Pylint always generates errors when run on Jinja files. Some of these are
# spurious. Regexes to suppress spurious errors are given here.
to_ignore = frozenset([

    # Pylint header.
    re.compile(r'\*+\sModule\s\w+$'),

    # Pylint always warns about missing Jinja supports.
    re.compile(r'E:\s*\d+,\s*\d+:\s+Undefined variable\s+\'(environment|dummy)\'\s+\(undefined-variable\)$'),

    # Jinja sometimes re-uses internal function names.
    re.compile(r'E:\s*\d+,\s*\d+:\s+function already defined line \d+ \(function-redefined\)$'),

    # Output from jinja_pylint.py (the other one, not us) itself.
    re.compile('compiling to [^\s]+?\.\.\.$'),
    re.compile('running pylint on [^\s]+?\.\.\.$'),

    # Blank lines.
    re.compile('$'),
])

def _lint(self, path):
    '''
    Generic lint invoker that we'll curry below.
    '''
    p = subprocess.Popen([self.lint, path, '--errors-only'],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)
    # Pylint errors come out on stdout. Why? Who knows.
    stdout, _ = p.communicate()
    errors = []
    for line in [x.strip() for x in stdout.split('\n')]:
        if any((x.match(line) for x in to_ignore)):
            continue
        errors.append(line)
    self.assertListEqual(errors, [], '\n'.join(['%s:' % path] + errors))

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
        if f.lower().endswith('.py'):
            # Skip Python sources.
            continue
        name = 'test_%s' % regex.sub('_', f)
        path = os.path.join(root, f)
        setattr(TestPyLint, name, lambda self, path=path: _lint(self, path))

if __name__ == '__main__':
    unittest.main()
