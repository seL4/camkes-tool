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
from .Template import Templates, PLATFORMS, TEMPLATES
from . import macros, sizeof_probe, arch_helpers
