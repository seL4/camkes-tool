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

from camkes.ast import LiftedAST, Procedure
from camkes.internal.cacheb import Cache, prime_ast_hash
from camkes.internal.tests.utils import CAmkESTest

def dummy_ast():
    '''
    A simple AST we can use for testing basic functionality.
    '''
    p = Procedure()
    l = LiftedAST([p])
    return l

class TestCacheB(CAmkESTest):
    def test_directory_creation(self):
        '''
        The cache should be capable of creating necessary subdirectories under
        its root.
        '''
        root = os.path.join(self.mkdtemp(), 'non-existent')

        c = Cache(root)

        input = prime_ast_hash(dummy_ast())

        c.save(input, ['arg1', 'arg2'], [], 'hello world')
        c.flush()

    def test_basic(self):
        '''
        Test we can look up something we've just saved. Note that this test
        will not actually perform an on-disk lookup.
        '''
        root = self.mkdtemp()
        c = Cache(root)

        input = prime_ast_hash(dummy_ast())

        c.save(input, ['arg1', 'arg2'], [], 'hello world')

        # Ensure we can find what we just saved.
        output = c.load(input, ['arg1', 'arg2'], [])

        self.assertEqual(output, 'hello world')

    def test_basic_with_flush(self):
        '''
        Same as the basic test, but we'll flush in-between to ensure we perform
        an on-disk lookup.
        '''
        root = self.mkdtemp()
        c = Cache(root)

        input = prime_ast_hash(dummy_ast())

        c.save(input, ['arg1', 'arg2'], [], 'hello world')
        c.flush()

        # Ensure we can find what we just saved.
        output = c.load(input, ['arg1', 'arg2'], [])

        self.assertEqual(output, 'hello world')

    def test_no_inputs(self):
        '''
        Ensure we can handle an entry with no inputs.
        '''
        root = self.mkdtemp()
        c = Cache(root)

        input = prime_ast_hash(LiftedAST([]))

        c.save(input, ['arg1', 'arg2'], [], 'hello world')

        # Ensure we can find what we just saved.
        output = c.load(input, ['arg1', 'arg2'], [])
        self.assertEqual(output, 'hello world')

        # Ensure it is preserved after a flush.
        c.flush()
        output = c.load(input, ['arg1', 'arg2'], [])
        self.assertEqual(output, 'hello world')

    def test_empty_output(self):
        root = self.mkdtemp()
        c = Cache(root)

        input = prime_ast_hash(dummy_ast())

        c.save(input, ['arg1', 'arg2'], [], '')

        # Ensure we can find what we just saved.
        output = c.load(input, ['arg1', 'arg2'], [])
        self.assertEqual(output, '')

        # Ensure it is preserved after a flush.
        c.flush()
        output = c.load(input, ['arg1', 'arg2'], [])
        self.assertEqual(output, '')

    def test_no_args(self):
        root = self.mkdtemp()
        c = Cache(root)

        input = prime_ast_hash(dummy_ast())

        c.save(input, [], [], 'hello world')

        # Ensure we can find what we just saved.
        output = c.load(input, [], [])
        self.assertEqual(output, 'hello world')

        # Ensure it is preserved after a flush.
        c.flush()
        output = c.load(input, [], [])
        self.assertEqual(output, 'hello world')

    def test_miss_in_memory(self):
        '''
        Test that an induced cache miss while the cache entry is still in
        memory works correctly.
        '''
        root = self.mkdtemp()
        c = Cache(root)

        input = prime_ast_hash(dummy_ast())

        c.save(input, ['arg1', 'arg2'], [], 'hello world')

        # Ensure we can find what we just saved.
        output = c.load(input, ['arg1', 'arg2'], [])
        self.assertEqual(output, 'hello world')

        # Now ensure we get a miss with a differing AST.
        input = prime_ast_hash(LiftedAST([]))
        output = c.load(input, ['arg1', 'arg2'], [])
        self.assertIsNone(output)

    def test_miss_in_memory2(self):
        '''
        Test that an induced cache miss while the cache entry is still in
        memory works correctly.
        '''
        root = self.mkdtemp()
        c = Cache(root)

        input = prime_ast_hash(dummy_ast())

        c.save(input, ['arg1', 'arg2'], [], 'hello world')

        # Ensure we can find what we just saved.
        output = c.load(input, ['arg1', 'arg2'], [])
        self.assertEqual(output, 'hello world')

        # Induce a miss by passing different arguments.
        output = c.load(input, ['arg1', 'arg2', 'arg3'], [])
        self.assertIsNone(output)

    def test_miss_on_disk1(self):
        '''
        Same as the in-memory miss test except we flush the cache in-between.
        '''
        root = self.mkdtemp()
        c = Cache(root)

        input = prime_ast_hash(dummy_ast())

        c.save(input, ['arg1', 'arg2'], [], 'hello world')
        c.flush()

        # Ensure we can find what we just saved.
        output = c.load(input, ['arg1', 'arg2'], [])
        self.assertEqual(output, 'hello world')

        # Now ensure we get a miss with a differing AST.
        input = prime_ast_hash(LiftedAST([]))
        output = c.load(input, ['arg1', 'arg2'], [])
        self.assertIsNone(output)

    def test_miss_from_missing_file1(self):
        '''
        Ensure cache misses from missing files function correctly.
        '''
        root = self.mkdtemp()
        c = Cache(root)

        input = prime_ast_hash(dummy_ast())

        _, tmp = tempfile.mkstemp()
        with open(tmp, 'wt') as f:
            f.write('foo bar')

        c.save(input, ['arg1', 'arg2'], [tmp], 'hello world')

        # Ensure we can find what we just saved.
        output = c.load(input, ['arg1', 'arg2'], [tmp])
        self.assertEqual(output, 'hello world')

        os.remove(tmp)

        c.flush()

        # Now ensure we get a miss after removing one of its inputs.
        output = c.load(input, ['arg1', 'arg2'], [tmp])
        self.assertIsNone(output)

    def test_miss_from_missing_file2(self):
        '''
        As above, but flush the entry to disk first.
        '''
        root = self.mkdtemp()
        c = Cache(root)

        input = prime_ast_hash(dummy_ast())

        _, tmp = tempfile.mkstemp()
        with open(tmp, 'wt') as f:
            f.write('foo bar')

        c.save(input, ['arg1', 'arg2'], [tmp], 'hello world')

        # Ensure we can find what we just saved.
        output = c.load(input, ['arg1', 'arg2'], [tmp])
        self.assertEqual(output, 'hello world')

        c.flush()

        os.remove(tmp)

        # Now ensure we get a miss after removing one of its inputs.
        output = c.load(input, ['arg1', 'arg2'], [tmp])
        self.assertIsNone(output)

    def test_timestamps(self):
        '''
        Ensure that modifying a timestamp on one of the inputs has no effect.
        '''
        root = self.mkdtemp()
        c = Cache(root)

        input = prime_ast_hash(dummy_ast())

        tmp = self.mkstemp()
        with open(tmp, 'wt') as f:
            f.write('foo bar')

        c.save(input, ['arg1', 'arg2'], [tmp], 'hello world')
        c.flush()

        # Bump the timestamps on the input.
        st = os.stat(tmp)
        os.utime(tmp, (st[stat.ST_ATIME] + 3600, st[stat.ST_MTIME] + 3600))

        # Ensure we can find what we just saved.
        output = c.load(input, ['arg1', 'arg2'], [tmp])
        self.assertEqual(output, 'hello world')

        # And after a flush.
        c.flush()
        output = c.load(input, ['arg1', 'arg2'], [tmp])
        self.assertEqual(output, 'hello world')

if __name__ == '__main__':
    unittest.main()
