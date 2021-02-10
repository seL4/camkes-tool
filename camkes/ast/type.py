#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#
#

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

NORMALISATION = {
    'integer'          : 'int',
    'signed int'       : 'int',
    'unsigned integer' : 'unsigned int',
    'character'        : 'character',
    'bool'             : 'boolean',
}

def normalise_type(type):
    try:
        return NORMALISATION[type]
    except KeyError:
        return type
