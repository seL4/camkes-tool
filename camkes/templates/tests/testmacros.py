#!/usr/bin/env python
# -*- coding: utf-8 -*-

#
# Copyright 2016, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''
This file contains unit test cases related to the template macros.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals

import os, re, subprocess, sys, unittest

ME = os.path.abspath(__file__)

# Make CapDL importable. Note that we just assume where it is in relation to
# our own directory.
sys.path.append(os.path.join(os.path.dirname(ME), '../../../../python-capdl'))

# Make CAmkES importable
sys.path.append(os.path.join(os.path.dirname(ME), '../../..'))

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

if __name__ == '__main__':
    unittest.main()
