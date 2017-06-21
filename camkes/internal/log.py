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

'''Internal logging interface.'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

import logging, sys

log = logging.getLogger('CAmkES')
logging.basicConfig(stream=sys.stderr)

def set_verbosity(verbosity):
    if verbosity == 0:
        log.setLevel(logging.CRITICAL + 1)
    elif verbosity == 2:
        log.setLevel(logging.INFO)
    elif verbosity == 3:
        log.setLevel(logging.DEBUG)
    else:
        log.setLevel(logging.WARNING)

# Expose convenience functions for logging.
def info(msg):      log.info(msg)
def warning(msg):   log.warning(msg)
def error(msg):     log.error(msg)
def debug(msg):     log.debug(msg)
def exception(msg): log.exception(msg)
def critical(msg):  log.critical(msg)
