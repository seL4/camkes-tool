#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#
#

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

from camkes.internal.exception import CAmkESError
import six

class TemplateError(CAmkESError):
    def __init__(self, content, entity=None):
        assert isinstance(content, six.string_types)
        if hasattr(entity, 'location') and entity.location is not None:
            msg = self._format_message(content, entity.location.filename,
                entity.location.lineno, entity.location.min_col,
                entity.location.max_col)
        else:
            msg = self._format_message(content)
        super(TemplateError, self).__init__(msg)
