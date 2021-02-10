#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#
#

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

import plyplus, re

# The directives that CPP emits to indicate a change of source file and/or line
# number.
LINE_DIRECTIVE = re.compile(
    r'\s*#\s*(?:line)?\s*(?P<lineno>\d+)(?:\s+"(?P<filename>[^"]*)")?.*$',
    flags=re.UNICODE)

class SourceLocation(object):
    '''
    The location of a parsed term in its original source file.

    This class is primarily useful for showing users useful error messages and
    for debugging. Note that "original source" above means the post-processed
    source if we are using CPP. This class looks more complicated than you may
    have expected because it parses CPP line directives, that are *not*
    interpreted by the stage 1 parser, in order to give the user source
    locations that match their own interpretation.
    '''

    def __init__(self, filename, term, full_source):
        assert plyplus.is_stree(term) or isinstance(term, plyplus.ParseError)
        self._filename = filename
        self._lineno = None
        self._min_col = None
        self._max_col = None
        self.term = term
        self.full_source = full_source
        # We defer narrowing the location because this can be expensive and
        # typically goes unused unless we hit a parse error.
        self.precise = False

    def _locate(self):
        '''
        Find the exact location we are referencing.
        '''

        if plyplus.is_stree(self.term):
            # First, force plyplus to calculate what it thinks the term's
            # location is.
            self.term.calc_position()

            plyplus_line = self.term.min_line
            self._min_col = self.term.min_col
            self._max_col = self.term.max_col

        else:
            assert isinstance(self.term, plyplus.ParseError)

            # Try to extract the line number from a plyplus error.
            m = re.search(r'^Syntax error in input at \'(?P<token>[^\']*)\' '
                r'\(type [^\)]*\) line\s+(?P<line>\d+)'
                r'(?:\s+col\s+(?P<col>\d+))?$',
                str(self.term), flags=re.MULTILINE)
            if m is not None:
                plyplus_line = int(m.group('line'))
                if m.group('col') is not None:
                    self._min_col = int(m.group('col'))
                    if len(m.group('token')) > 0:
                        self._max_col = self._min_col + len(m.group('token')) \
                            - 1
            else:
                plyplus_line = None

        if plyplus_line is None:
            # We have no opportunity to find a more precise location.
            self.precise = True
            return

        if self.full_source is None:
            self._lineno = plyplus_line
            self.precise = True
            return

        # Now parse the original source only looking for CPP line directives,
        # to adjust our understanding of the location if necessary.
        current_filename = self._filename
        current_lineno = 1
        for line_index, line in enumerate(self.full_source.split('\n')):
            if line_index + 1 == plyplus_line:
                # We've reached the line this term is on.
                self._filename = current_filename
                self._lineno = current_lineno
                self.precise = True
                return
            m = LINE_DIRECTIVE.match(line)
            if m is not None:
                # The current line is a line directive.
                if m.group('filename') is not None:
                    current_filename = m.group('filename')
                current_lineno = int(m.group('lineno'))
            else:
                # Standard (CAmkES) line.
                current_lineno += 1
        else:
            assert False, \
                'term line number points outside its containing source ' \
                '(plyplus bug?)'

    @property
    def filename(self):
        if not self.precise:
            self._locate()
        return self._filename

    @property
    def lineno(self):
        if not self.precise:
            self._locate()
        return self._lineno

    @property
    def min_col(self):
        if not self.precise:
            self._locate()
        return self._min_col

    @property
    def max_col(self):
        if not self.precise:
            self._locate()
        return self._max_col
