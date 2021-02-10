#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#
#

'''
A mapping from abstract CAmkES generated files to implementations for a
specific platform. Callers are intended to invoke `lookup` with a path to the
template they need, using dots as path separators. E.g. call
`lookup('seL4.seL4RPC.from.source')` to get the template for the source file
for the from end of a seL4RPC connector on seL4.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals

from .exception import TemplateError
from . import macros, arch_helpers
