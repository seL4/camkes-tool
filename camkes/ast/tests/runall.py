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

import os, sys, unittest

ME = os.path.abspath(__file__)

# Make camkes.ast importable
sys.path.append(os.path.join(os.path.dirname(ME), '../../..'))

from lint import TestLint
from lintsource import TestSourceLint
from testckeywords import TestCKeywords
from testhashing import TestHashingAssumptions
from testobjects import TestObjects

if __name__ == '__main__':
    unittest.main()
