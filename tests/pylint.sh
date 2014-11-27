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

# Run pylint over all relevant python files.

which pylint &>/dev/null || { echo "pylint not found" >&2 ; exit 1 ; }

export TOP_DIR=$(dirname $(readlink -f $0))/..

function lint() {
    echo "Checking $(basename $1)..."
    pylint --rcfile=/dev/null --errors-only "$1"
    if [ $? -ne 0 ]; then
        exit 255
    else
        exit 0
    fi
}
export -f lint

find ${TOP_DIR}/camkes -name '*.py' \
 | sort \
 | xargs -n 1 -i bash -c 'lint "$@"' _ {}
