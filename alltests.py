#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

'''
This script is a quick way to execute the tests for all CAmkES modules.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from concurrencytest import ConcurrentTestSuite, fork_for_tests
import capdl
import camkes.ast
import camkes.internal
import camkes.parser
import camkes.runner
import camkes.templates

import argparse, multiprocessing, os, subprocess, sys, unittest

ME = os.path.abspath(__file__)

# Available tests. The keys to this dictionary should be names of packages containing tests
# packages must be imported in this file and the directory with tests must be a valid
# python module (--> contains an __init__.py)
TESTS = ['ast', 'internal', 'parser','runner','templates']

def main(argv):
    parser = argparse.ArgumentParser(prog=argv[0],
        description='run CAmkES tests')
    parser.add_argument('--jobs', '-j', nargs='?', type=int,
        help='parallelise test execution')
    parser.add_argument('--verbosity', '-v', default=1, type=int, help="Verbosity to run tests. 0 = quiet. 1 = default. 2 = verbose")
    parser.add_argument('test', nargs='*', choices=TESTS+['all'], default='all', help='run a specific category of tests')
    parser.add_argument('--capdl-python', help='Deprecated. Using this argument has no effect.')
    options = parser.parse_args(argv[1:])

    if options.jobs is None:
        # Maximum parallelism.
        options.jobs = multiprocessing.cpu_count()

    # work out which tests to run
    if options.test == 'all' or 'all' in options.test:
        test_packages = TESTS
    else:
        test_packages = options.test

    # load the tests we want to run
    loader = unittest.TestLoader()
    test_suite = unittest.TestSuite()
    for v in test_packages:
        test_suite.addTests(loader.discover('camkes.' + v, top_level_dir=os.path.dirname(ME)))

    concurrent_suite = ConcurrentTestSuite(test_suite, fork_for_tests(options.jobs))
    runner = unittest.TextTestRunner(verbosity=options.verbosity)
    result = runner.run(concurrent_suite)
    if result.wasSuccessful():
        return 0
    return 1

if __name__ == '__main__':
    sys.exit(main(sys.argv))
