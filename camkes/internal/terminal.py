#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#
#

'''
Home for utility functions for learning things about the terminal we're running
in.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

from .memoization import memoize
import os, subprocess, sys

# Various ANSI terminal control sequences. For now, we only define the ones we
# need.
BOLD = '\033[1m'
RED = '\033[31m'
RESET = '\033[0m'

@memoize()
def terminal_supports_colour():
    if not sys.stdout.isatty():
        return False
    try:
        with open(os.devnull, 'wt') as f:
            colours = subprocess.check_output(['tput', 'colors'], stderr=f)
    except (subprocess.CalledProcessError, OSError):
        return False
    try:
        return int(colours) > 0
    except ValueError:
        return False
