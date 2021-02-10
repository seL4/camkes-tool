#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#
#

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

from camkes.ast import LiftedAST
import abc, collections, six

class Parser(six.with_metaclass(abc.ABCMeta, object)):

    @abc.abstractmethod
    def parse_file(self, filename):
        raise NotImplementedError

    @abc.abstractmethod
    def parse_string(self, content):
        raise NotImplementedError

class Transformer(six.with_metaclass(abc.ABCMeta, Parser)):

    def __init__(self, subordinate_parser):
        assert isinstance(subordinate_parser, Parser)
        super(Transformer, self).__init__()
        self.subordinate = subordinate_parser

    def parse_file(self, filename):
        assert isinstance(filename, six.string_types)
        ast_lifted, read = self.subordinate.parse_file(filename)
        assert self.precondition(ast_lifted, read)
        result, result_read = self.transform(ast_lifted, read)
        assert self.postcondition(result, result_read)
        return result, result_read

    def parse_string(self, string):
        assert isinstance(string, six.string_types)
        ast_lifted, read = self.subordinate.parse_string(string)
        assert self.precondition(ast_lifted, read)
        result, result_read = self.transform(ast_lifted, read)
        assert self.postcondition(result, result_read)
        return result, result_read

    @abc.abstractmethod
    def precondition(self, ast_lifted, read):
        assert isinstance(ast_lifted, LiftedAST)
        assert isinstance(read, collections.Iterable)
        raise NotImplementedError

    @abc.abstractmethod
    def postcondition(self, ast_lifted, read):
        assert isinstance(ast_lifted, LiftedAST)
        assert isinstance(read, collections.Iterable)
        raise NotImplementedError

    @abc.abstractmethod
    def transform(self, ast_lifted, read):
        assert isinstance(ast_lifted, LiftedAST)
        assert isinstance(read, collections.Iterable)
        raise NotImplementedError
