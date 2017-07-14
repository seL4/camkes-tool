#!/bin/bash
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

# Wrapper script for calling the CAmkES code generator. You should use this as
# an entry point in preference to calling Python files directly because it
# checks the dependencies for you.

# If the user has the CAmkES accelerator enabled, first try to see if it can
# retrieve the requested output from the level A cache. Note that the
# accelerator returns non-zero on a cache miss and we just fall back on running
# the CAmkES code generator.
if [ -n "${CONFIG_CAMKES_ACCELERATOR}" ]; then
    camkes-accelerator "${@}"
    if [ $? -eq 0 ]; then
        exit 0
    fi
fi

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

if [ -z "${PYTHONPATH}" ]; then
    export PYTHONPATH=${DIR}
else
    export PYTHONPATH=${PYTHONPATH}:${DIR}
fi

# Default optimisation (none).
O=

# Allow the user to override the Python runtime.
if [ ! -z "${CONFIG_CAMKES_PYTHON_INTERPRETER_PYPY}" ]; then
    PYTHON=pypy
elif [ ! -z "${CONFIG_CAMKES_PYTHON_INTERPRETER_FIGLEAF}" ]; then
    PYTHON=figleaf
elif [ ! -z "${CONFIG_CAMKES_PYTHON_INTERPRETER_COVERAGE}" ]; then
    PYTHON="python-coverage run"
else
    if [ ! -z "${CONFIG_CAMKES_PYTHON_INTERPRETER_CPYTHON2}" ]; then
        PYTHON=python2
    elif [ ! -z "${CONFIG_CAMKES_PYTHON_INTERPRETER_CPYTHON3}" ]; then
        PYTHON=python3
    else
        PYTHON=python
    fi
    if [ ! -z "${CONFIG_CAMKES_PYTHON_OPTIMISE_BASIC}" ]; then
        O=-O
    elif [ ! -z "${CONFIG_CAMKES_PYTHON_OPTIMISE_MORE}" ]; then
        O=-OO
    fi
fi

${PYTHON} ${O} -m camkes.runner "${@}"
