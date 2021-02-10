#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#
#

'''
Deterministic string hashing.

By default, string types in Python are hashed using a scheme that is not stable
across platforms or, in some cases, even different executions on the same
platform. This is a problem for us when we need to persist hashes on disk and
then compare them later to determine if input is unchanged. Here we provide an
alternative hash that is stable.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

import hashlib, six

def hash_string(s):
    if isinstance(s, six.text_type):
        s = s.encode('utf-8')
    return hashlib.sha256(s).hexdigest()

def strhash(s):
    return int(hash_string(s), 16)
