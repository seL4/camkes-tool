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
Apply various static analysis tools to the accelerator.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals

import os, re, subprocess, sys, unittest

ME = os.path.abspath(__file__)
MY_DIR = os.path.dirname(ME)

# Make CAmkES importable
sys.path.append(os.path.join(MY_DIR, '../..'))

from camkes.internal.tests.utils import CAmkESTest, which

# License server for the Goanna static analyser. You need a valid license to
# run Goanna, which we have internally at NICTA, but you'll need to be able to
# reach this server.
GOANNA_LICENSE_SERVER = 'goanna.research.nicta.com.au'

def goanna_license_server_reachable():
    try:
        with open(os.devnull, 'w') as f:
            subprocess.check_call(['ping', '-c', '1', '-w', '5',
                GOANNA_LICENSE_SERVER], stdout=f, stderr=f)
        return True
    except subprocess.CalledProcessError:
        return False

GOANNA_WRAPPER = os.path.join(MY_DIR, '../goanna_wrapper.py')

class TestStaticAnalysis(CAmkESTest):
    @unittest.skipIf(which('cmake') is None or which('goannacc') is None or
        not goanna_license_server_reachable(), 'CMake or Goanna not found or '
        'Goanna license server unavailable')
    def test_goanna_compilation(self):
        '''
        Test whether the Goanna static analyser can find any problems with the
        accelerator.
        '''

        # Build the accelerator with Goanna. We use GNU Make here to avoid the
        # output of Ninja (which it appears there is no way to hide) getting in
        # the way.
        tmp = self.mkdtemp()
        ret, stdout, stderr = self.execute(['cmake', '-G', 'Unix Makefiles',
            MY_DIR], cwd=tmp, env=dict(os.environ.items() + [('CC',
            GOANNA_WRAPPER), ('CFLAGS', '--license-server=%s' %
            GOANNA_LICENSE_SERVER)]))
        if ret != 0:
            self.fail('cmake failed:\n%s\n%s' % (stdout, stderr))
        ret, stdout, stderr = self.execute(['make', 'camkes-accelerator'],
            cwd=tmp)
        if ret != 0:
            self.fail('goannacc failed to compile the accelerator:\n%s' %
                stderr)

        # Check if we saw any warnings.
        warning_line = re.compile(r'(?P<relfile>[^\s]+):(?P<lineno>\d+):'
            r'\s*warning:\s*Goanna\[(?P<checkname>[^\]]+)\]\s*Severity-'
            r'(?P<severity>\w+),\s*(?P<message>[^\.]*)\.\s*(?P<rules>.*)$')
        for line in [x.strip() for x in stderr.split('\n') if x.strip() != '']:
            if warning_line.match(line):
                self.fail('Goanna found new issues with the accelerator '
                    'source:\n%s' % stderr)

    @unittest.skipIf(which('cmake') is None or which('ninja') is None or which('scan-build') is None, 'CMake or Ninja or scan-build not found')
    def test_clang_static_analyser(self):
        '''
        Run the Clang static analyser on the accelerator.
        '''
        tmp = self.mkdtemp()
        ret, stdout, stderr = self.execute(['scan-build', '--status-bugs',
            'cmake', '-G', 'Ninja', MY_DIR], cwd=tmp)
        if ret != 0:
            self.fail('cmake failed:\n%s\n%s' % (stdout, stderr))
        ret, stdout, stderr = self.execute(['ninja', 'camkes-accelerator'],
            cwd=tmp)
        if ret != 0:
            self.fail('scan-build failed:\n%s\n%s' % (stdout, stderr))

    @unittest.skipIf(which('cppcheck') is None, 'cppcheck not found')
    def test_cppcheck(self):
        '''
        Run the Cppcheck static analyser on the accelerator.
        '''
        accelerator = os.path.join(MY_DIR, 'accelerator.c')
        ret, stdout, stderr = self.execute(['cppcheck', '--error-exitcode=-1',
            '--library=gnu.cfg', accelerator])
        if ret != 0:
            self.fail('%s\n%s' % (stdout, stderr))

if __name__ == '__main__':
    unittest.main()
