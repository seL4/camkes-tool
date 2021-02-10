#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#
#

'''
An object representation of an integer. This is frustratingly necessary for
expressing things like a counter in a Jinja template that can be modified
within a loop.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

class Counter(object):
    def __init__(self):
        self.value = 0

    def set(self, value):
        self.value = value

    def __repr__(self):
        return str(self.value)

    def increment(self, offset=1):
        self.value += offset

    def decrement(self, offset=1):
        self.value -= offset
