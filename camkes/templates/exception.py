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

class TemplateError(CAmkESError):
    def __init__(self, content, entity=None):
        assert isinstance(content, six.string_types)
        msg = []
        if hasattr(entity, 'filename') and \
                isinstance(entity.filename, six.string_types):
            msg.append('%s:' % entity.filename)
        if hasattr(entity, 'lineno') and isinstance(entity.lineno,
                six.integer_types + six.string_types):
            msg.append('%s:' % entity.lineno)
        if len(msg) > 0:
            msg.append(' ')
        msg.append(content)
        super(TemplateError, self).__init__(''.join(msg))
