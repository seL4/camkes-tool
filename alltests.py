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
This script is a quick way to execute the tests for all CAmkES modules.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals

import argparse, multiprocessing, os, subprocess, sys

ME = os.path.abspath(__file__)

# Available tests. The keys to this dictionary should be category names and the
# values should be executable files at either absolute paths or relative paths
# to this directory.
TESTS = {
    'ast':['camkes/ast/tests/runall.py'],
    'internal':['camkes/internal/tests/runall.py'],
    'parser':['camkes/parser/tests/runall.py'],
    'runner':['camkes/runner/tests/runall.py'],
    'templates':['camkes/templates/tests/runall.py'],
    'accelerator':['tools/accelerator/alltests.py'],
}

def run(command):
    sys.stdout.write('running %s...\n' % ' '.join(command))
    p = subprocess.Popen(command, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, universal_newlines=True)
    stdout, stderr = p.communicate()
    return command, p.returncode, stdout, stderr

def main(argv):
    parser = argparse.ArgumentParser(prog=argv[0],
        description='run CAmkES tests')
    parser.add_argument('--jobs', '-j', nargs='?', type=int,
        help='parallelise test execution')
    parser.add_argument('test', nargs='*', help='run a specific category of tests')
    options = parser.parse_args(argv[1:])

    try:
        tests = [[os.path.join(os.path.dirname(ME), t[0])] + t[1:] for t in
            ([TESTS[t] for t in options.test] or TESTS.values())]
    except KeyError as e:
        sys.stderr.write('invalid test category %s\n' % e)
        return -1

    if options.jobs is None:
        # Maximum parallelism.
        options.jobs = min(len(tests), multiprocessing.cpu_count())

    if options.jobs > 1:
        # XXX: This is just a map using a thread pool, but
        # `multiprocessing.Pool.map` seems to not handle Ctrl-C very well.
        def mapper(f, xs):
            return multiprocessing.Pool(options.jobs).map_async(f,
                xs).get(sys.maxint)
    else:
        mapper = map

    # Run the tests.
    results = mapper(run, tests)

    # Dump the stdout and stderr of each test.
    for command, _, stdout, stderr in results:
        if stdout:
            sys.stdout.write(' -- stdout %s --\n%s' %
                (' '.join(command), stdout))
        if stderr:
            sys.stderr.write(' -- stderr %s --\n%s' %
                (' '.join(command), stderr))

    # Return non-zero if any of the tests fail.
    return any(r for _, r, _, _ in results)

if __name__ == '__main__':
    sys.exit(main(sys.argv))
