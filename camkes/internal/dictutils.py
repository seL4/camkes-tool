#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#
#

'''Various helpers for doing advanced things with dictionaries.'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

import re

def get_fields(s):
    '''Return a set of field names referenced as formatting keys in the given
    string. I thought there would be an easier way to get this, but I can't
    find one. E.g. get_fields('%(hello)s %(world)s') returns
    set('hello', 'world').'''
    return set(re.findall(r'%\(([^)]+)\)', s))

class Guard(object):
    '''Representation of a condition required for some action. See usage in
    Template.py.'''
    def __init__(self, guard_fn):
        self.guard_fn = guard_fn

    def __call__(self, arg):
        return self.guard_fn(arg)
