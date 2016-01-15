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

from camkes.internal.exception import CAmkESError
import six

class ParseError(CAmkESError):
    def __init__(self, content, location=None, filename=None, lineno=None):
        assert isinstance(content, six.string_types) or isinstance(content, Exception)
        if location is not None:
            filename = location.filename
            lineno = location.lineno
        msg = self._format_message(six.text_type(content), filename, lineno)
        super(ParseError, self).__init__(msg)
