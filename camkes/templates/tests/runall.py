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

from jinja_lint import TestLint
from jinja_pylint import TestPyLint
from lint import TestPyLintOnSource
from lintsource import TestSourceLint
from testbadidioms import TestBadIdioms
from testcustomtemplates import TestCustomTemplates
from testsel4_async import TestSel4Async
from testmacros import TestMacros

if __name__ == '__main__':
    unittest.main()
