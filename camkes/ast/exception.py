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

class ASTError(CAmkESError):
    '''
    An error resulting from inconsistency detected in the AST.
    '''
    def __init__(self, message, entity):
        self.entity = entity
        msg = self._format_message(message, entity.filename, entity.lineno)
        super(ASTError, self).__init__(msg)
