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

class ParseError(Exception):
    def __init__(self, content, filename=None, lineno=None):
        assert isinstance(content, six.string_types) or isinstance(content, Exception)
        self.content = content
        self.filename = filename
        self.lineno = lineno
        msg = []
        if filename is not None:
            msg.append('%s:' % filename)
        if lineno is not None:
            msg.append('%d:' % lineno)
        if len(msg) > 0:
            msg.append(' ')
        msg.append(six.text_type(content))
        super(ParseError, self).__init__(''.join(msg))
