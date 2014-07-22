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

# Test whether the parser and all AST objects can be imported in isolation into
# a containing python script without errors.

which python &>/dev/null || { echo "python not found" >&2 ; exit 1 ; }

for i in ast parser runner templates lint; do
    echo "Importing camkes.${i}..."
    python -c "import camkes.${i}"
    if [ $? -ne 0 ]; then
        exit 1
    fi
done
