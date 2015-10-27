#!/usr/bin/env python
# -*- coding: utf-8 -*-

#
# Copyright 2015, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

from __future__ import absolute_import, division, print_function, \
    unicode_literals

import os, shutil, stat, subprocess, sys, tempfile, unittest

ME = os.path.abspath(__file__)

# Make CAmkES importable
sys.path.append(os.path.join(os.path.dirname(ME), '../../..'))

from camkes.internal.tests.utils import CAmkESTest, cpp_available
from camkes.parser.stage0 import CPP

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

if __name__ == '__main__':
    unittest.main()
