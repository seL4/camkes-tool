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
