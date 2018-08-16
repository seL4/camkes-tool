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
'''
Query parser. The following parser is designed to accept a stage 7 parser,
whose output it consumes. This parser's purpose is to resolve settings that
reference other attributes.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals

from camkes.ast.objects import QueryObject
from .base import Transformer

# Re-use the post-condition of the stage 6 parser as our pre-condition; that
# only a single assembly remains.
from .stage6 import postcondition as precondition
from .exception import ParseError
import abc
import argparse
import logging
import re
import six

from pyfdt.pyfdt import FdtBlobParse

class Query(six.with_metaclass(abc.ABCMeta, object)):
    """A Query is a named function in the Camkes ADL that takes arguments. Classes that implement this interface
    can resolve queries into python dicts in the Camkes AST."""

    def __init__(self):
        self.options = None

    @abc.abstractmethod
    def resolve(self, *args):
        """Resolve a query. This method should return a list of dicts which match the query results. """
        pass

    @abc.abstractmethod
    def get_parser(self):
        """Get a command line argument parser for this query. This allows command line arguments to be passed
        to specific types of queries"""
        pass

    @abc.abstractmethod
    def check_options(self):
        """Validate the options field of a query instance."""

    @abc.abstractmethod
    def get_query_name(self):
        """return the name of this query that allows it to be matched with a query class"""

    def parse_args(self, argv):
        """Parse command line arguments for this query. Set the parsed arguments to self.options."""
        self.options, argv = self.get_parser().parse_known_args(args=argv)
        self.check_options()
        return argv

    def get_deps(self):
        """Return any dependent files used by this query"""
        return []


class DtbMatchQuery(Query):
    """Convert a dtb query into a dictionary of results from the device tree"""
    def __init__(self):
        self.dtb = None

    def resolve(self, *args):
        # for now just return a list of empty strings as the result
        return [""]

    def get_parser(self):
        parser = argparse.ArgumentParser('dtb')
        parser.add_argument('--dtb',
                            type=str,
                            help='Flattened device tree blob (.dtb) to query for device tree properties.',
                            required=True)
        return parser

    def check_options(self):
        try:
            with open(self.options.dtb, 'rb') as dtb_file:
                self.dtb = FdtBlobParse(dtb_file).to_fdt()
        except:
            logging.fatal("Failed to parse dtb file {0}".format(self.options.dtb.name))

    def get_query_name(self):
        return "dtb"

    def get_deps(self):
        return [self.options.dtb]

def print_query_parser_help():
    """Print a help string from all query parsers"""

    for subclass in Query.__subclasses__():
        subclass().get_parser().print_help()


def parse_query_parser_args(argv):
    """Return a dict of namespace <-> instantiated query object for any queries matching argv"""

    queries = {}
    for subclass in Query.__subclasses__():
        query = subclass()
        queries[subclass.get_query_name()] = query
        argv = query.parse_args(argv)

    return queries, argv


def postcondition(ast_lifted):
    '''
    All Queries are resolved.
    '''
    return all(not isinstance(x.value, QueryObject) for x in
               ast_lifted.assembly.configuration.settings)

def resolve(ast_lifted, read, queries):
    '''
    Resolve all Queries to their return values.
    '''

    assembly = ast_lifted.assembly
    new_settings = []
    used_queries = set()

    key_regexp = re.compile(r'^\w+$')
    for s in assembly.configuration.settings:
        if isinstance(s.value, QueryObject):
            query_obj = s.value
            if query_obj.type in queries:
                query = queries.get(query_obj.type)
                result = query.resolve(query_obj.args)
                # if we aren't looking up a value in the dict returned by the query,
                # return the entire dict, which comes out as a struct in the attribute.
                # Queries however may have non-alphanumeric characters
                # that cannot be used in C structs - so convert those characters in keys
                # to '_'
                if not query_obj.dict_lookup:
                    for (key, value) in result.items():
                        del result[key]
                        if not key_regexp.match(key):
                            key = re.sub('\W', '_', key)
                        result[key] = value
                    s.value = result
                else:
                    s.value = result
                    for key in query_obj.dict_lookup.lookup:
                        s.value = s.value[key]
                used_queries.add(query)
            else:
                raise ParseError("unknown query {0}".format(query_obj.type))
        new_settings.append(s)

    for q in used_queries:
        for dep in q.get_deps():
            read.add(dep)

    assembly.configuration.settings = new_settings


class QueryParseStage(Transformer):
    def __init__(self, subordinate_parser, queries):
        super(QueryParseStage, self).__init__(subordinate_parser)
        self.queries = queries

    def precondition(self, ast_lifted, _):
        return precondition(ast_lifted)

    def postcondition(self, ast_lifted, _):
        return postcondition(ast_lifted)

    def transform(self, ast_lifted, read):
        resolve(ast_lifted, read, self.queries)
        return ast_lifted, read

