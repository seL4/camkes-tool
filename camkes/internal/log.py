#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''Internal logging interface.'''

import logging, sys

log = logging.getLogger('CAmkES')
log.addHandler(logging.StreamHandler(sys.stderr))

def set_verbosity(verbosity):
    if verbosity == 0:
        log.setLevel(logging.CRITICAL + 1)
    elif verbosity == 2:
        log.setLevel(logging.INFO)
    elif verbosity == 3:
        log.setLevel(logging.DEBUG)
    else:
        log.setLevel(logging.WARNING)

def set_stream(stream):
    while len(log.handlers) > 0:
        log.removeHandler(log.handlers[0])
    log.addHandler(logging.StreamHandler(stream))

# Expose convenience functions for logging.
def info(msg):      log.info(msg)
def warning(msg):   log.warning(msg)
def error(msg):     log.error(msg)
def debug(msg):     log.debug(msg)
def exception(msg): log.exception(msg)
def critical(msg):  log.critical(msg)
