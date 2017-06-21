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
Tests that the CAmkES accelerator correctly interoperates with the native level
A cache accessor.

The level A cache is accessed natively in CAmkES by
camkes.internal.cachea.Cache. The accelerator, meanwhile, reads entries from the
level A cache and is responsible for determining whether CAmkES itself should be
run. Thus it is crucial that the entries written by the native level A cache
access should be read and interpreted by the accelerator in the same way as they
would be read and interpreted by the native reader. The following tests this
behaviour.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals

import os, re, six, sys, tempfile, unittest

ME = os.path.abspath(__file__)
MY_DIR = os.path.dirname(ME)

# Make CAmkES importable
sys.path.append(os.path.join(MY_DIR, '../..'))

from camkes.internal.cachea import Cache, prime_inputs
from camkes.internal.tests.utils import CAmkESTest, which
from camkes.internal.version import version

VALGRIND = ['valgrind', '--leak-check=yes', '--track-origins=yes']

def valgrind_found_leak(stderr):
    return re.search(r'ERROR SUMMARY: 0 errors', stderr) is None

class TestCacheAInterop(CAmkESTest):
    def setUp(self):
        super(TestCacheAInterop, self).setUp()
        tmp = self.mkdtemp()
        ret, stdout, stderr = self.execute(['cmake', '-G', 'Ninja', MY_DIR],
            cwd=tmp)
        if ret != 0:
            self.fail('cmake failed:\n%s\n%s' % (stdout, stderr))
        ret, _, stderr = self.execute(['ninja', 'camkes-accelerator'], cwd=tmp)
        if ret != 0:
            self.fail('could not build accelerator:\n%s' % stderr)
        self.accelerator = os.path.join(tmp, 'camkes-accelerator')

        tmp = self.mkdtemp()
        ret, stdout, stderr = self.execute(['cmake', '-D'
            'CMAKE_BUILD_TYPE=Debug', '-G', 'Ninja', MY_DIR], cwd=tmp)
        if ret != 0:
            self.fail('cmake failed:\n%s\n%s' % (stdout, stderr))
        ret, _, stderr = self.execute(['ninja', 'camkes-accelerator'], cwd=tmp)
        if ret != 0:
            self.fail('could not build debug accelerator:\n%s' % stderr)
        self.debug_accelerator = os.path.join(tmp, 'camkes-accelerator')

    def test_basic_invocation(self):
        '''
        Make sure we actually built a usable accelerator binary.
        '''
        ret, _, stderr = self.execute([self.accelerator, '--version'])
        if ret != 0:
            self.fail('camkes-accelerator --version failed:\n%s' % stderr)

    def test_no_args(self):
        '''
        Confirm that the accelerator anticipates the case of no arguments.
        '''
        ret, _, stderr = self.execute([self.accelerator])
        self.assertNotEqual(ret, 0)

        six.assertRegex(self, stderr,
            re.compile(r'^\s*no arguments provided\s*$'))

    def test_no_cache(self):
        '''
        Confirm the accelerator fails in an expected way when there is no
        cache.
        '''
        tmp = self.mkdtemp()
        root = os.path.join(tmp, 'non-existent')

        output = self.mkstemp()

        ret, stdout, stderr = self.execute([self.accelerator, '--outfile', output])
        self.assertNotEqual(ret, 0)
        self.assertEqual(stdout, '')
        self.assertEqual(stderr, '')

    def test_basic(self):
        '''
        Test we can save and retrieve something (expected case).
        '''
        root = self.mkdtemp()

        # CAmkES internally suffixes the root with a couple of things to
        # namespace the cache.
        internal_root = os.path.join(root, version(), 'cachea')
        c = Cache(internal_root)

        # Construct some fake inputs.
        input1 = self.mkstemp()
        with open(input1, 'wt') as f:
            f.write('hello world')
        input2 = self.mkstemp()
        with open(input2, 'wt') as f:
            f.write('foo bar')
        inputs = prime_inputs([input1, input2])

        # And a fake working directory.
        cwd = self.mkdtemp()

        # Imagine we were saving the output from the following file.
        output = self.mkstemp()

        # So the command line arguments would be:
        args = ['--cache-dir', root, '--outfile', output]

        # Save the entry. Note that we truncate the args because the runner and
        # the accelerator strip --outfile arguments before interacting with the
        # cache.
        c.save(args[:-2], cwd, 'moo cow', inputs)
        c.flush()

        # We're done with the native cache.
        del c

        # Now let's try to read back the cache entry from the accelerator.
        ret, _, _ = self.execute([self.accelerator] + args, cwd=cwd)
        self.assertEqual(ret, 0)

        # If it worked, we should have the output in the expected place.
        with open(output, 'rt') as f:
            data = f.read()
        self.assertEqual(data, 'moo cow')

    def test_cache_miss_inputs(self):
        '''
        Test that we correctly miss when one of the inputs has changed.
        '''
        # As for the basic test case...
        root = self.mkdtemp()

        internal_root = os.path.join(root, version(), 'cachea')
        c = Cache(internal_root)

        input1 = self.mkstemp()
        with open(input1, 'wt') as f:
            f.write('hello world')
        input2 = self.mkstemp()
        with open(input2, 'wt') as f:
            f.write('foo bar')
        inputs = prime_inputs([input1, input2])

        cwd = self.mkdtemp()

        output = self.mkstemp()

        args = ['--cache-dir', root, '--outfile', output]

        c.save(args[:-2], cwd, 'moo cow', inputs)
        c.flush()

        del c

        # Now let's modify one of the inputs.
        with open(input2, 'at') as f:
            f.write('foo bar')

        ret, stdout, stderr = self.execute([self.accelerator] + args, cwd=cwd)

        # It should have missed (== non-zero return value with no output).
        self.assertNotEqual(ret, 0)
        self.assertEqual(stdout, '')
        self.assertEqual(stderr, '')

    def test_cache_miss_input_deleted(self):
        '''
        Test that we correctly miss when one of the inputs has been deleted.
        '''
        # As for the basic test case...
        root = self.mkdtemp()

        internal_root = os.path.join(root, version(), 'cachea')
        c = Cache(internal_root)

        input1 = self.mkstemp()
        with open(input1, 'wt') as f:
            f.write('hello world')
        _, input2 = tempfile.mkstemp()
        with open(input2, 'wt') as f:
            f.write('foo bar')
        inputs = prime_inputs([input1, input2])

        cwd = self.mkdtemp()

        output = self.mkstemp()

        args = ['--cache-dir', root, '--outfile', output]

        c.save(args[:-2], cwd, 'moo cow', inputs)
        c.flush()

        del c

        # Now let's delete one of the inputs.
        os.remove(input2)

        ret, stdout, stderr = self.execute([self.accelerator] + args, cwd=cwd)

        # It should have missed (== non-zero return value with no output).
        self.assertNotEqual(ret, 0)
        self.assertEqual(stdout, '')
        self.assertEqual(stderr, '')

    def test_cache_miss_args(self):
        '''
        Test that we correctly miss if the command line arguments have changed.
        '''
        # As for the basic test case...
        root = self.mkdtemp()

        internal_root = os.path.join(root, version(), 'cachea')
        c = Cache(internal_root)

        input1 = self.mkstemp()
        with open(input1, 'wt') as f:
            f.write('hello world')
        input2 = self.mkstemp()
        with open(input2, 'wt') as f:
            f.write('foo bar')
        inputs = prime_inputs([input1, input2])

        cwd = self.mkdtemp()

        output = self.mkstemp()

        args = ['--cache-dir', root, '--outfile', output]

        c.save(args[:-2], cwd, 'moo cow', inputs)
        c.flush()

        del c

        new_args = args + ['--cpp']
        ret, stdout, stderr = self.execute([self.accelerator] + new_args, cwd=cwd)

        # It should have missed (== non-zero return value with no output).
        self.assertNotEqual(ret, 0)
        self.assertEqual(stdout, '')
        self.assertEqual(stderr, '')

    def test_cache_miss_cwd(self):
        '''
        Test that we correctly miss if the working directory differs.
        '''
        # As for the basic test case...
        root = self.mkdtemp()

        internal_root = os.path.join(root, version(), 'cachea')
        c = Cache(internal_root)

        input1 = self.mkstemp()
        with open(input1, 'wt') as f:
            f.write('hello world')
        input2 = self.mkstemp()
        with open(input2, 'wt') as f:
            f.write('foo bar')
        inputs = prime_inputs([input1, input2])

        cwd = self.mkdtemp()

        output = self.mkstemp()

        args = ['--cache-dir', root, '--outfile', output]

        c.save(args[:-2], cwd, 'moo cow', inputs)
        c.flush()

        del c

        # Use a different working directory this time around.
        cwd = self.mkdtemp()

        ret, stdout, stderr = self.execute([self.accelerator] + args, cwd=cwd)

        # It should have missed (== non-zero return value with no output).
        self.assertNotEqual(ret, 0)
        self.assertEqual(stdout, '')
        self.assertEqual(stderr, '')

    def test_cache_hit_truncate(self):
        '''
        A previous accelerator bug resulted in the output file not being
        truncated before the accelerator wrote to it. The result was that an
        output resulting from a cache hit that was delivered via the
        accelerator would have trailing garbage if it was shorter than the
        existing file content. More specifically, the following sequence could
        occur:

          1. Build with cache A enabled and "short string" is output and
             cached;
          2. Build with different config and "a slightly longer string" is
             output (and cached);
          3. Build with original config and the accelerator enabled and "short
             string" is retrieved, but written without truncating the output.

        As a result, the final file content would end up as "short stringonger
        string". This test validates that this problem has not been
        reintroduced.
        '''

        root = self.mkdtemp()

        internal_root = os.path.join(root, version(), 'cachea')
        c = Cache(internal_root)

        # Setup a basic, single-input entry.
        input1 = self.mkstemp()
        with open(input1, 'wt') as f:
            f.write('hello world')
        inputs = prime_inputs([input1])

        cwd = self.mkdtemp()

        output = self.mkstemp()

        args = ['--cache-dir', root, '--outfile', output]

        # Write the entry to the cache with a specific short value.
        content = 'moo cow'
        c.save(args[:-2], cwd, content, inputs)
        c.flush()

        del c

        # Now write something *longer* into the output file.
        with open(output, 'wt') as f:
            f.write('some lengthier text')

        # Now run the accelerator to retrieve the original, shorter output.
        ret, stdout, stderr = self.execute([self.accelerator] + args, cwd=cwd)

        # It should have hit the cache and written the correct, shorter output.
        self.assertEqual(ret, 0)
        self.assertEqual(stdout, '')
        self.assertEqual(stderr, '')
        with open(output) as f:
            data = f.read()
        self.assertEqual(data, content)

    # Various Valgrind tests of the above follow. Note that they try to trigger
    # any problems in the debug version of the accelerator first because we get
    # more precise backtraces in the Valgrind output when debugging symbols are
    # available.

    @unittest.skipIf(which('valgrind') is None, 'valgrind not found')
    def test_no_args_valgrind(self):
        _, _, stderr = self.execute(VALGRIND + [self.debug_accelerator])
        if valgrind_found_leak(stderr):
            self.fail('camkes-accelerator with no arguments leaks memory:\n%s'
                % stderr)

        _, _, stderr = self.execute(VALGRIND + [self.accelerator])
        if valgrind_found_leak(stderr):
            self.fail('camkes-accelerator with no arguments leaks memory (not '
                'reproducible in debug mode):\n%s' % stderr)

    @unittest.skipIf(which('valgrind') is None, 'valgrind not found')
    def test_no_cache_valgrind(self):
        tmp = self.mkdtemp()
        root = os.path.join(tmp, 'non-existent')

        output = self.mkstemp()

        _, _, stderr = self.execute(VALGRIND + [self.debug_accelerator, '--outfile',
            output])
        if valgrind_found_leak(stderr):
            self.fail('camkes-accelerator --outfile %s leaks memory:\n%s' %
                (output, stderr))

        _, _, stderr = self.execute(VALGRIND + [self.accelerator, '--outfile', output])
        if valgrind_found_leak(stderr):
            self.fail('camkes-accelerator --outfile %s leaks memory (not '
                'reproducible in debug mode):\n%s' % (output, stderr))

    @unittest.skipIf(which('valgrind') is None, 'valgrind not found')
    def test_basic_valgrind(self):
        root = self.mkdtemp()

        # CAmkES internally suffixes the root with a couple of things to
        # namespace the cache.
        internal_root = os.path.join(root, version(), 'cachea')
        c = Cache(internal_root)

        # Construct some fake inputs.
        input1 = self.mkstemp()
        with open(input1, 'wt') as f:
            f.write('hello world')
        input2 = self.mkstemp()
        with open(input2, 'wt') as f:
            f.write('foo bar')
        inputs = prime_inputs([input1, input2])

        # And a fake working directory.
        cwd = self.mkdtemp()

        # Imagine we were saving the output from the following file.
        output = self.mkstemp()

        # So the command line arguments would be:
        args = ['--cache-dir', root, '--outfile', output]

        # Save the entry. Note that we truncate the args because the runner and
        # the accelerator strip --outfile arguments before interacting with the
        # cache.
        c.save(args[:-2], cwd, 'moo cow', inputs)
        c.flush()

        # We're done with the native cache.
        del c

        # Now let's try to read back the cache entry from the accelerator.
        _, _, stderr = self.execute(VALGRIND + [self.debug_accelerator] + args, cwd=cwd)
        if valgrind_found_leak(stderr):
            self.fail('camkes-accelerator %s leaks memory:\n%s' %
                (' '.join(args), stderr))

        _, _, stderr = self.execute(VALGRIND + [self.accelerator] + args, cwd=cwd)
        if valgrind_found_leak(stderr):
            self.fail('camkes-accelerator %s leaks memory (not reproducible '
                'in debug mode):\n%s' % (' '.join(args), stderr))

    @unittest.skipIf(which('valgrind') is None, 'valgrind not found')
    def test_cache_miss_inputs_valgrind(self):
        # As for the basic test case...
        root = self.mkdtemp()

        internal_root = os.path.join(root, version(), 'cachea')
        c = Cache(internal_root)

        input1 = self.mkstemp()
        with open(input1, 'wt') as f:
            f.write('hello world')
        input2 = self.mkstemp()
        with open(input2, 'wt') as f:
            f.write('foo bar')
        inputs = prime_inputs([input1, input2])

        cwd = self.mkdtemp()

        output = self.mkstemp()

        args = ['--cache-dir', root, '--outfile', output]

        c.save(args[:-2], cwd, 'moo cow', inputs)
        c.flush()

        del c

        # Now let's modify one of the inputs.
        with open(input2, 'at') as f:
            f.write('foo bar')

        _, _, stderr = self.execute(VALGRIND + [self.debug_accelerator] + args, cwd=cwd)
        if valgrind_found_leak(stderr):
            self.fail('camkes-accelerator %s leaks memory:\n%s' %
                (' '.join(args), stderr))

        _, _, stderr = self.execute(VALGRIND + [self.accelerator] + args, cwd=cwd)
        if valgrind_found_leak(stderr):
            self.fail('camkes-accelerator %s leaks memory (not reproducible '
                'in debug mode):\n%s' % (' '.join(args), stderr))

    @unittest.skipIf(which('valgrind') is None, 'valgrind not found')
    def test_cache_miss_input_deleted_valgrind(self):
        # As for the basic test case...
        root = self.mkdtemp()

        internal_root = os.path.join(root, version(), 'cachea')
        c = Cache(internal_root)

        input1 = self.mkstemp()
        with open(input1, 'wt') as f:
            f.write('hello world')
        _, input2 = tempfile.mkstemp()
        with open(input2, 'wt') as f:
            f.write('foo bar')
        inputs = prime_inputs([input1, input2])

        cwd = self.mkdtemp()

        output = self.mkstemp()

        args = ['--cache-dir', root, '--outfile', output]

        c.save(args[:-2], cwd, 'moo cow', inputs)
        c.flush()

        del c

        # Now let's delete one of the inputs.
        os.remove(input2)

        _, _, stderr = self.execute(VALGRIND + [self.debug_accelerator] + args, cwd=cwd)
        if valgrind_found_leak(stderr):
            self.fail('camkes-accelerator %s leaks memory:\n%s' %
                (' '.join(args), stderr))

        _, _, stderr = self.execute(VALGRIND + [self.accelerator] + args, cwd=cwd)
        if valgrind_found_leak(stderr):
            self.fail('camkes-accelerator %s leaks memory (not reproducible '
                'in debug mode):\n%s' % (' '.join(args), stderr))

    @unittest.skipIf(which('valgrind') is None, 'valgrind not found')
    def test_cache_miss_args_valgrind(self):
        # As for the basic test case...
        root = self.mkdtemp()

        internal_root = os.path.join(root, version(), 'cachea')
        c = Cache(internal_root)

        input1 = self.mkstemp()
        with open(input1, 'wt') as f:
            f.write('hello world')
        input2 = self.mkstemp()
        with open(input2, 'wt') as f:
            f.write('foo bar')
        inputs = prime_inputs([input1, input2])

        cwd = self.mkdtemp()

        output = self.mkstemp()

        args = ['--cache-dir', root, '--outfile', output]

        c.save(args[:-2], cwd, 'moo cow', inputs)
        c.flush()

        del c

        new_args = args + ['--cpp']

        _, _, stderr = self.execute(VALGRIND + [self.debug_accelerator] + new_args,
            cwd=cwd)
        if valgrind_found_leak(stderr):
            self.fail('camkes-accelerator %s leaks memory:\n%s' %
                (' '.join(args), stderr))

        _, _, stderr = self.execute(VALGRIND + [self.accelerator] + new_args, cwd=cwd)
        if valgrind_found_leak(stderr):
            self.fail('camkes-accelerator %s leaks memory (not reproducible '
                'in debug mode):\n%s' % (' '.join(args), stderr))

    @unittest.skipIf(which('valgrind') is None, 'valgrind not found')
    def test_cache_miss_cwd_valgrind(self):
        # As for the basic test case...
        root = self.mkdtemp()

        internal_root = os.path.join(root, version(), 'cachea')
        c = Cache(internal_root)

        input1 = self.mkstemp()
        with open(input1, 'wt') as f:
            f.write('hello world')
        input2 = self.mkstemp()
        with open(input2, 'wt') as f:
            f.write('foo bar')
        inputs = prime_inputs([input1, input2])

        cwd = self.mkdtemp()

        output = self.mkstemp()

        args = ['--cache-dir', root, '--outfile', output]

        c.save(args[:-2], cwd, 'moo cow', inputs)
        c.flush()

        del c

        # Use a different working directory this time around.
        cwd = self.mkdtemp()

        _, _, stderr = self.execute(VALGRIND + [self.debug_accelerator] + args, cwd=cwd)
        if valgrind_found_leak(stderr):
            self.fail('camkes-accelerator %s leaks memory:\n%s' %
                (' '.join(args), stderr))

        _, _, stderr = self.execute(VALGRIND + [self.accelerator] + args, cwd=cwd)
        if valgrind_found_leak(stderr):
            self.fail('camkes-accelerator %s leaks memory (not reproducible '
                'in debug mode):\n%s' % (' '.join(args), stderr))

if __name__ == '__main__':
    unittest.main()
