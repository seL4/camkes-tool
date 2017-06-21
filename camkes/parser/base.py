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
