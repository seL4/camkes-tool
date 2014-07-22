#!/bin/bash
#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

# Check that the import example runs without errors.

TOP_DIR=$(dirname $(readlink -f $0))/..

${TOP_DIR}/examples/direct-ast-access/example-import.py >/dev/null
