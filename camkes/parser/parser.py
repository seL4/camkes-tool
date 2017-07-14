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

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

from .base import Parser as BaseParser
from .stage0 import CPP, Reader
from .stage1 import Parse1
from .stage2 import Parse2
from .stage3 import Parse3
from .stage4 import Parse4
from .stage5 import Parse5
from .stage6 import Parse6
from .stage7 import Parse7
from .stage8 import Parse8
from .stage9 import Parse9
from .stage10 import Parse10
import os

class Parser(BaseParser):
    def __init__(self, options=None):

        # Build the file reader.
        if hasattr(options, 'cpp') and options.cpp:
            toolprefix = os.environ.get('TOOLPREFIX', '')
            if hasattr(options, 'cpp_flag'):
                flags = options.cpp_flag
            else:
                flags = []
            s0 = CPP(toolprefix, flags)
        else:
            s0 = Reader()

        # Build the plyplus parser
        s1 = Parse1(s0)

        # Build the import resolver.
        if hasattr(options, 'import_path'):
            import_path = options.import_path
        else:
            import_path = []
        s2 = Parse2(s1, import_path)

        # Build the lifter.
        s3 = Parse3(s2, debug=hasattr(options, 'verbosity') and
            options.verbosity > 2)

        # Build the reference resolver.
        allow_forward = hasattr(options, 'allow_forward_references') and \
            options.allow_forward_references
        s4 = Parse4(s3, allow_forward)

        # Build the group collapser.
        s5 = Parse5(s4)

        # Build the assembly combiner.
        s6 = Parse6(s5)

        # Build the component hierarchy flattener.
        s7 = Parse7(s6)

        # Build the attribute resolver.
        s8 = Parse8(s7)

        # Build the N-1 connection combiner.
        s9 = Parse9(s8)

        # Build the AST freezer.
        s10 = Parse10(s9)

        self.parser = s10

    def parse_file(self, filename):
        return self.parser.parse_file(filename)

    def parse_string(self, string):
        return self.parser.parse_string(string)

def parse_file(filename, options=None):
    p = Parser(options)
    return p.parse_file(filename)

def parse_string(string, options=None):
    p = Parser(options)
    return p.parse_string(string)
