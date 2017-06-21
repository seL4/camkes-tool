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
mkdir -p

For some reason, there does not seem to be a simpler way of achieving thread-
safe directory creation in Python.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

import errno, os

def mkdirp(path):
    assert not os.path.exists(path) or os.path.isdir(path)
    try:
        os.makedirs(path)
    except OSError as e:
        # Mask any errors that result from the directory existing.
        if e.errno != errno.EEXIST or not os.path.isdir(path):
            raise
