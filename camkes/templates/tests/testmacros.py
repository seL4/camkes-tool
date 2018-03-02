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
This file contains unit test cases related to the template macros.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals

import ast, fnmatch, os, re, subprocess, sys, unittest

ME = os.path.abspath(__file__)
MY_DIR = os.path.dirname(ME)

# Make CapDL importable. Note that we just assume where it is in relation to
# our own directory.
sys.path.append(os.path.join(MY_DIR, '../../../../python-capdl'))

# Make CAmkES importable
sys.path.append(os.path.join(MY_DIR, '../../..'))

from camkes.internal.tests.utils import CAmkESTest, which
from camkes.templates.macros import sizeof

def uname():
    '''
    Determine the hardware architecture of this machine. Note that we're only
    really interested in x86 or x86_64.
    '''
    try:
        machine = subprocess.check_output(['uname', '-m']).strip()
    except subprocess.CalledProcessError:
        return None
    if re.match(r'i\d86$', machine):
        return 'x86'
    return machine

class TestMacros(CAmkESTest):

    @unittest.skipIf(which('g++') is None or uname() not in ('x86', 'x86_64'),
        'x86[_64] g++ not available')
    def test_sizeof_x86(self):
        '''
        Test that the size of standard types are what we expect when targeting
        x86. This might seem obvious, but this test can fail on an x86_64 host
        if `sizeof` does not take into account that we are actually targeting
        x86 (32-bit).
        '''
        os.environ['TOOLPREFIX'] = ''

        sz = sizeof('ia32', 'long')

        self.assertEqual(sz, 4)

    def test_find_unused_macros(self):
        '''
        Find macros intended for the templates that are never actually used in
        any template.
        '''

        # First obtain a set of available macros by parsing the source of
        # macros.py.
        macrospy = os.path.join(MY_DIR, '../macros.py')
        with open(macrospy) as f:
            source = f.read()

        node = ast.parse(source, filename=macrospy)

        macros = set()
        for i in ast.iter_child_nodes(node):
            if isinstance(i, ast.FunctionDef):
                macros.add(i.name)

        # Next get a set of gitignored globs.

        # First up, ignore the tests.
        ignored = set(('%s/**' % MY_DIR,))

        # Now look at all .gitignores from three directories up.
        for stem in ('../../..', '../..', '..'):
            gitignore = os.path.join(MY_DIR, stem, '.gitignore')
            if os.path.exists(gitignore):
                with open(gitignore) as f:
                    for line in (x.strip() for x in f
                            if x.strip() != '' and not x.startswith('#')):
                        pattern = os.path.join(os.path.abspath(
                            os.path.dirname(gitignore)), line)
                        ignored.add(pattern)

        # Now let's look at all the templates and note macro calls.

        # A regex to match macro calls from the template context. Note that it is
        # imprecise, so the resulting analysis could generate false negatives.
        call = re.compile(r'/\*[-\?].*?\bmacros\.([a-zA-Z][a-zA-Z0-9_]*)\b')

        used = set()
        for root, _, files in os.walk(os.path.abspath(
                os.path.join(MY_DIR, '..'))):
            for f in (os.path.join(root, f) for f in files):
                for pattern in ignored:
                    try:
                        if fnmatch.fnmatchcase(f, pattern):
                            break
                    except Exception:
                        # Suppress any errors resulting from invalid lines in
                        # .gitignore.
                        pass
                else:
                    # This file did not match any of the ignore patterns; scan
                    # it for macro calls.

                    with open(f) as input:
                        source = input.read()
                    for m in call.finditer(source):
                        used.add(m.group(1))

        # HACK: This exceptions list is a temporary hack for some macros that
        # are used in a future iteration of the Isabelle label mapping theory.
        # It should be removed when the label mapping theory is updated.
        EXCEPTIONS = set(['capdl_sorter', 'to_isabelle_set'])

        unused = macros - used - EXCEPTIONS
        if len(unused) > 0:
            [print("Unused macro: %s" % u) for u in unused]
        self.assertLen(unused, 0)

if __name__ == '__main__':
    unittest.main()
