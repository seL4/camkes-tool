#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#
#

'''
Implementation of an immutable dict.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

import collections

class frozendict(collections.Mapping):
    def __init__(self, dictionary=None):
        self._d = dictionary or {}

    def __getitem__(self, key):
        return self._d[key]

    def __iter__(self):
        return iter(self._d)

    def __len__(self):
        return len(self._d)
