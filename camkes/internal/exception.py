#!/usr/bin/env python
# -*- coding: utf-8 -*-

#
# Copyright 2016, NICTA
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

class CAmkESError(Exception):
    '''
    Generic basis for CAmkES errors.
    '''
    @staticmethod
    def _format_message(message, filename=None, lineno=None, min_col=None,
            max_col=None):
        msg = []
        if filename is not None:
            msg.extend([filename, ':'])
        if lineno is not None:
            msg.extend([str(lineno), ':'])
            if min_col is not None:
                msg.extend([str(min_col), ':'])
        if len(msg) > 0:
            msg.append(' ')
        msg.append(message)
        return ''.join(msg)
