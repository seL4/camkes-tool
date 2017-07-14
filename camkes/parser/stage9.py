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
Stage 9 parser. The following parser is designed to accept a stage 8 parser,
whose output it consumes.
Combine n-1 connections according to the following rule:
1. If an interface is in multiple connections, and in each connection it is
   on the same end (to or from), and in each connection it is the only interface
   on its end, all the connections can be combined into a single connection.
2. If an interface is in multiple connections and the condition in 1 does not
   hold, the spec is invalid.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

from camkes.ast.objects import Connection, ConnectionEnd

from .base import Transformer
from .exception import ParseError

# A collection of connections that groups connections based only
# the interfaces in them. Can be used to consolidate multiple
# connections to a single interface into a single N-1 connection
# to that interface.
class ConnectionTracker:
    def __init__(self):
        # Dicts mapping connection ends  to sets of
        # connection ends at the other end of the
        # connection
        self.to_candidates = {}
        self.from_candidates = {}

        # Dict mapping connection ends to sets of
        # connections where the key is the only connection end
        # on one of the sides of the connection
        self.connections = {}

        # Dict mapping connection ends to types
        self.types = {}

        # Set of connection ends
        # that have appeared in sides of connections with multiple
        # interfaces. If an interface in this set appears in the spec
        # more than once then the spec is invalid.
        self.ignored = set()

    def repeated_interface_error(self, end):
        raise ParseError("Multiple connections involving %s. "
                "In at least one, %s isn't on the '1' side of an N-1 connection"
                % (str(end), str(end)))

    def _add_connection_ends(self, ends, other_ends,
            candidates, other_candidates, connection):

        assert len(ends) > 0

        ignored_ends = self.ignored & ends
        if ignored_ends:
            # an interface has appeard multiple times
            self.repeated_interface_error(ignored_ends.pop())

        if len(ends) == 1:
            end = ends.pop()

            if str(end) in {str(k) for k in other_candidates.keys()}:
                # interface appears on the other side of a connection
                # somewhere else in the spec
                raise ParseError("Interface %s appears on to and from side of connections." % str(end))

            if end not in candidates:
                candidates[end] = set()

            already_connected = candidates[end] & other_ends
            if already_connected:
                already_connected_end = already_connected.pop()
                # one of the interfaces on the other side of this connection
                # is already connected to this interface
                raise ParseError("Multiple connections between interfaces %s and %s."
                        % (str(end), str(already_connected_end)))

            candidates[end] |= other_ends

            if end not in self.connections:
                self.connections[end] = set()

            self.connections[end].add(connection)

            if end not in self.types:
                self.types[end] = connection.type
            elif self.types[end] != connection.type:
                # we've already seen a connection to this interface, but it
                # was of a different type
                raise ParseError("Multiple connectors used in connections involving %s. (%s, %s)"
                        % (str(end), self.types[end].name, connection.type.name))

        else:
            ignored_ends = ends & set(self.connections.keys())
            if ignored_ends:
                # an interface has appeard multiple times
                self.repeated_interface_error(ignored_ends.pop())

            self.ignored |= ends

    # track a connection
    def add(self, connection):
        self._add_connection_ends(set(connection.to_ends), set(connection.from_ends),
                self.to_candidates, self.from_candidates, connection)
        self._add_connection_ends(set(connection.from_ends), set(connection.to_ends),
                self.from_candidates, self.to_candidates, connection)

    def _consolidate_direction(self, direction, candidates):
        for end in sorted(candidates.keys(), key=str):
            other_ends = candidates[end]
            if len(self.connections[end]) > 1:
                name = ".".join([c.name for c in self.connections[end]])
                sorted_other_ends = sorted(other_ends, key=str)
                if direction == 'from':
                    from_ends = [end]
                    to_ends = sorted_other_ends
                else:
                    from_ends = sorted_other_ends
                    to_ends = [end]
                new_connection = Connection(self.types[end], name, from_ends, to_ends)

                yield (self.connections[end], new_connection)

    # yields tuples of the form  (conns_to_remove, conn_to_add) where conns_to_remove
    # is a set of connections to remove from the ast, and
    # conn_to_add is a single connection to replace them with
    def consolidate(self):
        for c in self._consolidate_direction('to', self.to_candidates):
            yield c
        for c in self._consolidate_direction('from', self.from_candidates):
            yield c

class Parse9(Transformer):
    def precondition(self, ast_lifted, _):
        return True

    def postcondition(self, ast_lifted, _):
        return True

    def transform(self, ast_lifted, read):

        tracker = ConnectionTracker()

        for connection in ast_lifted.assembly.connections:
            tracker.add(connection)

        for (conns_to_remove, conn_to_add) in tracker.consolidate():
            for c in conns_to_remove:
                ast_lifted.assembly.connections.remove(c)
            ast_lifted.assembly.connections.append(conn_to_add)

        return ast_lifted, read
