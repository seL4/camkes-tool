#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#
#

'''
Stage 9 parser. The following parser is designed to accept a stage 8 parser,
whose output it consumes.
Combine n-1 connections according to the following rule:
1. If an interface is in multiple connections, and in each connection it is
   on the same end (to or from), all the connections can be combined into a single connection.
2. If an interface is in multiple connections and the condition in 1 does not
   hold, the spec is invalid.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from future.utils import iteritems
from itertools import chain
from camkes.internal.seven import cmp, filter, map, zip

from camkes.ast.objects import Connection, ConnectionEnd

from .base import Transformer
from .exception import ParseError


# track a connection
def add_connections(connections):
    candidates = {}
    for connection in connections:
        for i in chain(connection.to_ends, connection.from_ends):
            if i in candidates:
                candidates[i].add(connection)
            else:
                candidates[i] = {connection}
    return candidates


# yields tuples of the form  (conns_to_remove, conn_to_add) where conns_to_remove
# is a set of connections to remove from the ast, and
# conn_to_add is a single connection to replace them with
def consolidate(candidates):
    multi = []
    for (_, i) in iteritems(candidates):
        # Combine connection sets if any two sets share a connection
        for j in multi:
            if i & j:
                j |= i
                break
        else:
            multi.append(i)

    # We have now combined all of the multi connection definitions

    for connections in multi:
        if len(connections) == 1:
            continue
        name = ".".join(sorted([c.name for c in connections]))
        to_ends = {end for c in connections for end in c.to_ends}
        from_ends = {end for c in connections for end in c.from_ends}
        connection_type = None
        for c in connections:
            if connection_type is not None:
                if c.type != connection_type:
                    raise ParseError("Multiple connectors used in connections involving %s. (%s, %s)"
                                     % (c.name, connection_type, c.type))

                assert c.type == connection_type, "Bad type"
            else:
                connection_type = c.type
        new_connection = Connection(connection_type, name, list(from_ends), list(to_ends))
        yield(connections, new_connection)


class Parse9(Transformer):
    def precondition(self, ast_lifted, _):
        return True

    def postcondition(self, ast_lifted, _):
        return True

    def transform(self, ast_lifted, read):

        candidates = add_connections(ast_lifted.assembly.connections)

        for (conns_to_remove, conn_to_add) in consolidate(candidates):
            for c in conns_to_remove:
                ast_lifted.assembly.connections.remove(c)
            ast_lifted.assembly.connections.append(conn_to_add)

        return ast_lifted, read
