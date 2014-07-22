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

# The parser in this repository contains several output modules (OutputCAmkES,
# etc.). This script generates the boiler plate for a new output
# module if you are creating one.

SOURCE=$(dirname $(readlink -f $0))/../parser
OBJ_SOURCES="GenericObjects ADLObjects IDLObjects"

cat <<EOT
#!/usr/bin/env python

from GenericObjects import *
from ADLObjects import *
from IDLObjects import *
import Printer as base

class Printer(base.Printer):
EOT
for fn in `grep "^    def show_" "${SOURCE}/Printer.py" | sort | uniq | sed 's/    def \(.*\)(self, o):/\1/g' | grep -v "show_reference"`; do
    obj=`echo ${fn:5:1} | tr '[:lower:]' '[:upper:]'`${fn:6}
    cat <<EOT
    def ${fn}(o):
        assert isinstance(o, ${obj})
        return 'FILL ME IN'

EOT
done
