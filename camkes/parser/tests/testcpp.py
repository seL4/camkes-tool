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

import os, shutil, stat, subprocess, sys, tempfile, unittest

ME = os.path.abspath(__file__)

# Make CAmkES importable
sys.path.append(os.path.join(os.path.dirname(ME), '../../..'))

from camkes.internal.tests.utils import CAmkESTest, cpp_available
from camkes.parser.stage0 import CPP, parse_makefile_rule

class TestCPP(CAmkESTest):
    def setUp(self):
        super(TestCPP, self).setUp()
        self.reader = CPP()

    @unittest.skipIf(not cpp_available(), 'CPP not found')
    def test_empty_string(self):
        content, read = self.reader.parse_string('')

    @unittest.skipIf(not cpp_available(), 'CPP not found')
    def test_basic_string(self):
        content, read = self.reader.parse_string('hello world')
        self.assertIn('hello', content)
        self.assertIn('world', content)

    @unittest.skipIf(not cpp_available(), 'CPP not found')
    def test_unicode_string(self):
        content, read = self.reader.parse_string('↑hello world')
        self.assertIn('↑', content)
        self.assertIn('hello', content)
        self.assertIn('world', content)

    @unittest.skipIf(not cpp_available(), 'CPP not found')
    def test_empty_file(self):
        tmp = self.mkstemp()
        with open(tmp, 'wt') as f:
            f.write('hello world')

        content, read = self.reader.parse_file(tmp)

        self.assertIn('hello', content)
        self.assertIn('world', content)
        self.assertIn(tmp, read)

    @unittest.skipIf(not cpp_available(), 'CPP not found')
    def test_non_existent_file(self):
        # Create a path that we know refers to a file that doesn't exist
        _, tmp = tempfile.mkstemp()
        os.remove(tmp)
        assert not os.path.exists(tmp)

        with self.assertRaises(Exception):
            self.reader.parse_file(tmp)

    @unittest.skipIf(not cpp_available(), 'CPP not found')
    def test_include(self):
        parent = self.mkstemp()
        child = self.mkstemp()

        with open(child, 'wt') as f:
            f.write('hello world')

        with open(parent, 'wt') as f:
            f.write('hello world\n#include "%s"' % child)

        _, read = self.reader.parse_file(parent)

        self.assertIn(parent, read)
        self.assertIn(child, read)

    @unittest.skipIf(not cpp_available(), 'CPP not found')
    def test_toolprefix(self):
        # Find CPP.
        cpp = subprocess.check_output(['which', 'cpp'],
            universal_newlines=True).strip()

        # Create a fake CPP.
        tmp = self.mkdtemp()
        toolprefix = 'my-toolprefix-'
        fake_cpp = os.path.join(tmp, '%scpp' % toolprefix)
        with open(fake_cpp, 'wt') as f:
            f.write('#!/bin/bash\n%s "$@"\n' % cpp)
        os.chmod(fake_cpp, stat.S_IRWXU)

        # Create some fake input.
        parent = self.mkstemp()
        child = self.mkstemp()
        with open(child, 'wt') as f:
            f.write('component foo {}\n')
        with open(parent, 'wt') as f:
            f.write('#include "%s"\n' % child)

        # Change the value of $PATH to affect the exec inside parse_string,
        # such that the original CPP won't be found. We want to do this to
        # ensure the test doesn't accidentally succeed because `toolprefix` is
        # ignored and we happen to exec the original CPP directly.
        old_path = os.environ['PATH']
        os.environ['PATH'] = tmp

        try:
            # Confirm CPP is not directly accessible.
            with self.assertRaises(OSError):
                with open(os.devnull, 'wt') as f:
                    subprocess.check_call(['cpp', '--version'], stdout=f,
                        stderr=f)

            # Make sure the stage 0 parser agrees with us.
            with self.assertRaises(OSError):
                p = CPP()
                p.parse_string('')

            # Now confirm it can see and use our fake CPP.
            parser = CPP(toolprefix)

            content, read = parser.parse_file(parent)

            self.assertIn('component', content)
            self.assertIn(parent, read)
            self.assertIn(child, read)

        finally:
            # Reset the environment.
            os.environ['PATH'] = old_path

    @unittest.skipIf(not cpp_available(), 'CPP not found')
    def test_flags(self):
        content, _ = self.reader.parse_string('HELLO')
        self.assertNotIn('world', content)

        parser = CPP(flags=['-DHELLO=world'])
        content, _ = parser.parse_string('HELLO')

        self.assertIn('world', content)

    # The following tests probe the behaviour of the parse_makefile_rule
    # function which has been buggy in the past.

    def test_no_cpp_rules(self):
        '''
        Test that an empty list of Makefile rules yields no dependencies.
        '''
        filename = self.mkstemp()

        # Create the file with no content.
        with open(filename, 'wt') as f:
            pass

        # Confirm that we get no dependencies out of it.
        with open(filename) as f:
            deps = list(parse_makefile_rule(f))
        self.assertLen(deps, 0)

    def test_basic_cpp_rule(self):
        '''
        Test that we can correctly handle a basic Makefile rule.
        '''
        filename = self.mkstemp()

        # Create a basic rule.
        with open(filename, 'wt') as f:
            f.write('target: a b\n')

        # Confirm we get the correct dependencies.
        with open(filename) as f:
            deps = set(parse_makefile_rule(f))
        self.assertSetEqual(deps, set(['a', 'b']))

    def test_split_cpp_rule(self):
        '''
        Test that we can correctly handle rules split over multiple lines.
        '''
        filename = self.mkstemp()

        # Create a split rule.
        with open(filename, 'wt') as f:
            f.write('target: a b \\\n'
                    'c \\\n'
                    'd\n')

        # Confirm we get the correct dependencies.
        with open(filename) as f:
            deps = set(parse_makefile_rule(f))
        self.assertSetEqual(deps, set(['a', 'b', 'c', 'd']))

    def test_split_cpp_rule2(self):
        '''
        Test a more complicated split rule.
        '''
        filename = self.mkstemp()

        # Create a complicated split rule.
        with open(filename, 'wt') as f:
            f.write('target: \\\n'
                    'a b \\\n'
                    '\\\n'
                    'c\n')

        # Confirm we get the correct dependencies.
        with open(filename) as f:
            deps = set(parse_makefile_rule(f))
        self.assertSetEqual(deps, set(['a', 'b', 'c']))

    def test_multiple_cpp_rules(self):
        '''
        We should ignore everything after the first Makefile dependency rule.
        Test that this is actually true.
        '''
        filename = self.mkstemp()

        # Create a file with multiple rules.
        with open(filename, 'wt') as f:
            f.write('target: a b c\n'
                    'target2: d e f\n')

        # Confirm we only get the dependencies of the first rule.
        with open(filename) as f:
            deps = set(parse_makefile_rule(f))
        self.assertSetEqual(deps, set(['a', 'b', 'c']))

if __name__ == '__main__':
    unittest.main()
