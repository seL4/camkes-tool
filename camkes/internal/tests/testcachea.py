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

import os, stat, sys, tempfile, unittest

ME = os.path.abspath(__file__)

# Make CAmkES importable
sys.path.append(os.path.join(os.path.dirname(ME), '../../..'))

from camkes.internal.cachea import Cache, prime_inputs
from camkes.internal.tests.utils import CAmkESTest

class TestCacheA(CAmkESTest):
    def test_directory_creation(self):
        '''
        The cache should be capable of creating necessary subdirectories under
        its root.
        '''
        root = os.path.join(self.mkdtemp(), 'non-existent')

        c = Cache(root)

        input = self.mkstemp()
        with open(input, 'wt') as f:
            f.write('foo bar')

        inputs = prime_inputs([input])

        c.save(['arg1', 'arg2'], os.getcwd(), 'hello world', inputs)
        c.flush()

    def test_basic(self):
        '''
        Test we can look up something we've just saved. Note that this test
        will not actually perform an on-disk lookup.
        '''
        root = self.mkdtemp()
        c = Cache(root)

        input = self.mkstemp()
        with open(input, 'wt') as f:
            f.write('foo bar')

        inputs = prime_inputs([input])

        cwd = os.getcwd()
        c.save(['arg1', 'arg2'], cwd, 'hello world', inputs)

        # Ensure we can find what we just saved.
        output = c.load(['arg1', 'arg2'], cwd)

        self.assertEqual(output, 'hello world')

    def test_basic_with_flush(self):
        '''
        Same as the basic test, but we'll flush in-between to ensure we perform
        an on-disk lookup.
        '''
        root = self.mkdtemp()
        c = Cache(root)

        input = self.mkstemp()
        with open(input, 'wt') as f:
            f.write('foo bar')

        inputs = prime_inputs([input])

        cwd = os.getcwd()
        c.save(['arg1', 'arg2'], cwd, 'hello world', inputs)
        c.flush()

        # Ensure we can find what we just saved.
        output = c.load(['arg1', 'arg2'], cwd)

        self.assertEqual(output, 'hello world')

    def test_no_inputs(self):
        '''
        Ensure we can handle an entry with no inputs.
        '''
        root = self.mkdtemp()
        c = Cache(root)

        inputs = prime_inputs([])

        cwd = os.getcwd()
        c.save(['arg1', 'arg2'], cwd, 'hello world', inputs)

        # Ensure we can find what we just saved.
        output = c.load(['arg1', 'arg2'], cwd)
        self.assertEqual(output, 'hello world')

        # Ensure it is preserved after a flush.
        c.flush()
        output = c.load(['arg1', 'arg2'], cwd)
        self.assertEqual(output, 'hello world')

    def test_empty_output(self):
        root = self.mkdtemp()
        c = Cache(root)

        input = self.mkstemp()
        with open(input, 'wt') as f:
            f.write('foo bar')

        inputs = prime_inputs([input])

        cwd = os.getcwd()
        c.save(['arg1', 'arg2'], cwd, '', inputs)

        # Ensure we can find what we just saved.
        output = c.load(['arg1', 'arg2'], cwd)
        self.assertEqual(output, '')

        # Ensure it is preserved after a flush.
        c.flush()
        output = c.load(['arg1', 'arg2'], cwd)
        self.assertEqual(output, '')

    def test_no_args(self):
        root = self.mkdtemp()
        c = Cache(root)

        input = self.mkstemp()
        with open(input, 'wt') as f:
            f.write('foo bar')

        inputs = prime_inputs([input])

        cwd = os.getcwd()
        c.save([], cwd, 'hello world', inputs)

        # Ensure we can find what we just saved.
        output = c.load([], cwd)
        self.assertEqual(output, 'hello world')

        # Ensure it is preserved after a flush.
        c.flush()
        output = c.load([], cwd)
        self.assertEqual(output, 'hello world')

    def test_miss_in_memory(self):
        '''
        Test that an induced cache miss while the cache entry is still in
        memory works correctly.
        '''
        root = self.mkdtemp()
        c = Cache(root)

        input = self.mkstemp()
        with open(input, 'wt') as f:
            f.write('foo bar')

        inputs = prime_inputs([input])

        cwd = os.getcwd()
        c.save(['arg1', 'arg2'], cwd, 'hello world', inputs)

        # Now cause the entry to be invalid by modifying inputs.
        with open(input, 'wt') as f:
            f.write('bar foo')

        # Ensure we miss when now performing a lookup.
        output = c.load(['arg1', 'arg2'], cwd)
        self.assertIsNone(output)

    def test_miss_on_disk1(self):
        '''
        Same as the in-memory miss test except we flush the cache in-between.
        '''
        root = self.mkdtemp()
        c = Cache(root)

        input = self.mkstemp()
        with open(input, 'wt') as f:
            f.write('foo bar')

        inputs = prime_inputs([input])

        cwd = os.getcwd()
        c.save(['arg1', 'arg2'], cwd, 'hello world', inputs)
        c.flush()

        # Now cause the entry to be invalid by modifying inputs.
        with open(input, 'wt') as f:
            f.write('bar foo')

        # Ensure we miss when now performing a lookup.
        output = c.load(['arg1', 'arg2'], cwd)
        self.assertIsNone(output)

    def test_miss_on_disk2(self):
        '''
        Same as the in-memory miss test except we flush the cache in-between,
        at a point at which the entry is already invalid. The invalidity is not
        actually detected then, but the later lookup should still miss.
        '''
        root = self.mkdtemp()
        c = Cache(root)

        input = self.mkstemp()
        with open(input, 'wt') as f:
            f.write('foo bar')

        inputs = prime_inputs([input])

        cwd = os.getcwd()
        c.save(['arg1', 'arg2'], cwd, 'hello world', inputs)

        # Now cause the entry to be invalid by modifying inputs.
        with open(input, 'wt') as f:
            f.write('bar foo')

        # Flush the (now invalid) entry to disk.
        c.flush()

        # Ensure we miss when now performing a lookup.
        output = c.load(['arg1', 'arg2'], cwd)
        self.assertIsNone(output)

    def test_miss_from_missing_file1(self):
        '''
        Ensure cache misses from missing files function correctly.
        '''
        root = self.mkdtemp()
        c = Cache(root)

        _, input = tempfile.mkstemp()
        with open(input, 'wt') as f:
            f.write('foo bar')

        inputs = prime_inputs([input])

        cwd = os.getcwd()
        c.save(['arg1', 'arg2'], cwd, 'hello world', inputs)

        # Now cause the entry to be invalid by deleting its input.
        os.remove(input)

        # Ensure we miss when now performing a lookup.
        output = c.load(['arg1', 'arg2'], cwd)
        self.assertIsNone(output)

    def test_miss_from_missing_file2(self):
        '''
        As above, but flush the entry to disk first.
        '''
        root = self.mkdtemp()
        c = Cache(root)

        _, input = tempfile.mkstemp()
        with open(input, 'wt') as f:
            f.write('foo bar')

        inputs = prime_inputs([input])

        cwd = os.getcwd()
        c.save(['arg1', 'arg2'], cwd, 'hello world', inputs)
        c.flush()

        # Now cause the entry to be invalid by deleting its input.
        os.remove(input)

        # Ensure we miss when now performing a lookup.
        output = c.load(['arg1', 'arg2'], cwd)
        self.assertIsNone(output)

    def test_miss_from_missing_file3(self):
        '''
        As above, but flush the entry to disk after deleting the input.
        '''
        root = self.mkdtemp()
        c = Cache(root)

        _, input = tempfile.mkstemp()
        with open(input, 'wt') as f:
            f.write('foo bar')

        inputs = prime_inputs([input])

        cwd = os.getcwd()
        c.save(['arg1', 'arg2'], cwd, 'hello world', inputs)

        # Now cause the entry to be invalid by deleting its input.
        os.remove(input)

        c.flush()

        # Ensure we miss when now performing a lookup.
        output = c.load(['arg1', 'arg2'], cwd)
        self.assertIsNone(output)

    def test_timestamps(self):
        '''
        Ensure that modifying a timestamp on one of the inputs has no effect.
        '''
        root = self.mkdtemp()
        c = Cache(root)

        input = self.mkstemp()
        with open(input, 'wt') as f:
            f.write('foo bar')

        inputs = prime_inputs([input])

        cwd = os.getcwd()
        c.save(['arg1', 'arg2'], cwd, 'hello world', inputs)

        # Bump the timestamps on the input.
        st = os.stat(input)
        os.utime(input, (st[stat.ST_ATIME] + 3600, st[stat.ST_MTIME] + 3600))

        # Ensure we can find what we just saved.
        output = c.load(['arg1', 'arg2'], cwd)
        self.assertEqual(output, 'hello world')

        # And after a flush.
        c.flush()
        output = c.load(['arg1', 'arg2'], cwd)
        self.assertEqual(output, 'hello world')

if __name__ == '__main__':
    unittest.main()
