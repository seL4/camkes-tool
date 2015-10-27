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
