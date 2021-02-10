#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

from camkes.internal.exception import CAmkESError

class ASTError(CAmkESError):
    '''
    An error resulting from inconsistency detected in the AST.
    '''
    def __init__(self, message, entity):
        self.entity = entity
        if entity.location is not None:
            msg = self._format_message(message, entity.location.filename,
                entity.location.lineno, entity.location.min_col,
                entity.location.max_col)
        else:
            msg = self._format_message(message)
        super(ASTError, self).__init__(msg)
