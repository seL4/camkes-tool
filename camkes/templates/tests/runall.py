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

from jinja_lint import TestLint
from jinja_pylint import TestPyLint
from lint import TestPyLintOnSource
from lintsource import TestSourceLint
from testbadidioms import TestBadIdioms
from testcustomtemplates import TestCustomTemplates
from testsel4_notification import TestSel4Notification
from testmacros import TestMacros

if __name__ == '__main__':
    unittest.main()
