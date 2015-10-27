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

import six

def types_compatible(value, type):
    assert isinstance(type, six.string_types)

    return not (
        (isinstance(value, six.integer_types) and type != 'int') or
        (isinstance(value, float) and type not in ('double', 'float')) or
        (isinstance(value, six.string_types) and type != 'string') or
        (isinstance(value, list) and type != 'list') or
        (isinstance(value, dict) and type != 'dict'))
