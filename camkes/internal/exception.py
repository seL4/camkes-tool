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

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

from camkes.internal.terminal import BOLD, RED, RESET, terminal_supports_colour

def _get_line(filename, lineno):
    '''
    Retrieve a given line from a file.
    '''
    try:
        with open(filename, 'rt') as f:
            for no, line in enumerate(f, 1):
                if no == lineno:
                    return line
    except IOError:
        # File did not exist.
        pass
    return None

class CAmkESError(Exception):

    def __init__(self, lines):
        super(CAmkESError, self).__init__(*lines)

    '''
    Generic basis for CAmkES errors.
    '''
    @staticmethod
    def _format_message(message, filename=None, lineno=None, min_col=None,
            max_col=None):
        msg = []
        line = None

        if filename is not None:
            msg.extend([filename, ':'])
            if lineno is not None:
                # It is not particularly efficient to read a file that we have
                # already read, but we assume as we're on an error handling
                # path here that we don't care about efficiency.
                line = _get_line(filename, lineno)
        if lineno is not None:
            msg.extend([str(lineno), ':'])
            if min_col is not None:
                msg.extend([str(min_col), ':'])

        if len(msg) > 0:
            msg.append(' ')

        indent = sum(len(x) for x in msg)

        # If we retrieved the actual source line, try pretty printing it in the
        # error message.
        if line is not None:

            if min_col is not None and max_col is not None:
                msg.append(line[:min_col-1])
                if terminal_supports_colour():
                    msg.extend([RED, BOLD])
                msg.append(line[min_col-1:max_col])
                if terminal_supports_colour():
                    msg.append(RESET)
                msg.append(line[max_col:])
            else:
                msg.append(line)

            if min_col is not None:
                msg.extend([' ' * (indent + min_col - 1), '^'])
                if max_col is not None:
                    msg.append('^' * (max_col - min_col))
                msg.append('\n')

        msg.append(message)
        return ''.join(msg).split('\n')
