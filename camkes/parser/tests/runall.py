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

import os, sys, unittest

ME = os.path.abspath(__file__)

# Make camkes.parser importable
sys.path.append(os.path.join(os.path.dirname(ME), '../../..'))

from testcpp import TestCPP
from testexamples import TestExamples
from lint import TestLint
from lintsource import TestSourceLint
from testobjects import TestObjects
from testreader import TestReader
from teststage1 import TestStage1
from teststage2 import TestStage2
from teststage3 import TestStage3
from teststage4 import TestStage4
from teststage5 import TestStage5
from teststage6 import TestStage6
from teststage7 import TestStage7
from teststage8 import TestStage8
from teststage9 import TestStage9
from teststage10 import TestStage10

if __name__ == '__main__':
    unittest.main()
