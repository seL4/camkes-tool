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


# Wrapper script for calling any of the standalone parts of CAmkES. You should
# use this as an entry point in preference to calling Python files directly
# because it checks the dependencies for you.

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

if [ $# -lt 1 ]; then
    echo "Usage: $0 command args..." >&2
    exit 1
elif [ "$1" = "--help" ]; then
    echo "Invoke standalone CAmkES tools." >&2
    echo " Usage: $0 command args..." >&2
    echo -n " Valid commands are: "
    for i in $(ls ${DIR}/camkes/); do
        if [ -e "${DIR}/camkes/$i/__main__.py" ]; then
            echo -n "$i "
        fi
    done
    echo ""
    exit 0
fi

if [ -z "${CONFIG_CAMKES_DISABLE_PYTHON_IMPORT_CHECKS}" ]; then

    # Check we can import dependencies.
    for i in elftools capdl jinja2 ply; do
        python -c "import $i" &>/dev/null
        if [ $? -ne 0 ]; then
            echo "Python $i module not found in your PYTHONPATH" >&2
            exit 1
        fi
    done

    # We need a quite up to date version of the Python ELF tools with ARM support.
    python -c "import elftools.elf.enums as e; e.ENUM_E_MACHINE['EM_ARM']" &>/dev/null
    if [ $? -ne 0 ]; then
        echo "The available version of Python elftools does not have ARM support; please update" >&2
        exit 1
    fi

fi

if [ -z "${PYTHONPATH}" ]; then
    export PYTHONPATH=${DIR}
else
    export PYTHONPATH=${PYTHONPATH}:${DIR}
fi

COMMAND=$1
if [ ! -e "${DIR}/camkes/${COMMAND}/__main__.py" ]; then
    echo "Unknown command \"${COMMAND}\"" >&2
    exit 1
fi
shift

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
    PYTHON=python
    if [ ! -z "${CONFIG_CAMKES_PYTHON_OPTIMIZE}" ]; then
        O=-O
    fi
fi

${PYTHON} ${O} ${DIR}/camkes/${COMMAND}/__main__.py "${@}"
