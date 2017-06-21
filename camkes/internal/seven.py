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
Because sometimes six just isn't enough.

Various shims to provide a consistent environment between Python 2 and Python
3. Note, this is a home for things *not* already provided by `six`.
'''

# These imports are relevant for compatibility, but need to be included
# per-file as they meddle with Python's internal parser.
from __future__ import absolute_import, division, print_function, \
    unicode_literals

import itertools

# Python 3 does not have the `cmp` function, but it can be defined as follow.
def cmp(a, b):
    return (a > b) - (a < b)

# In Python 2, `filter`, `map` and `zip` return lists, whereas in Python 3 they
# return iterators. Try to force the Python 3 semantics.

try:
    from future_builtins import filter
except ImportError:
    try:
        from itertools import ifilter as filter
    except ImportError:
        filter = filter

try:
    from future_builtins import map
except ImportError:
    try:
        from itertools import imap as map
    except ImportError:
        map = map

try:
    from future_builtins import zip
except ImportError:
    try:
        from itertools import izip as zip
    except ImportError:
        zip = zip
