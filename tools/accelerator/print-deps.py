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
Script for generating extra dependencies (on the CAmkES sources) for the
top-level CAmkES Makefile.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals

import os, sys

# Make CAmkES importable.
sys.path.append(os.path.join(os.path.dirname(__file__), '../..'))
from camkes.internal.version import sources

for source, _ in sources():
    sys.stdout.write('%s\n' % source)
