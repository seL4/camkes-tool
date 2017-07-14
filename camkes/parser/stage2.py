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
Stage 2 parser. The following parser is designed to accept a stage 1 parser,
whose output it consumes. A stage 2 parser makes the following transformation:

    raw_ast ⇒ augmented_ast
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

from .base import Parser
from .exception import ParseError
import collections, os

class Parse2(Parser):
    def __init__(self, parse1, importpath=None):
        self.parse1 = parse1
        self.importpath = importpath or []

    def _resolve(self, source, filename, ast_raw, read):

        assert ast_raw.head == 'start', 'unexpected raw AST structure'
        ast_augmented = [(source, filename, t) for t in ast_raw.tail]

        queue = collections.deque(ast_augmented)
        final_ast_augmented = []

        while len(queue) > 0:
            source, filename, item = queue.popleft()

            if not hasattr(item, 'head'):
                # Empty statement.
                continue

            elif item.head == 'import':

                target = None

                assert len(item.tail) == 1, 'unexpected raw AST structure'

                import_type = item.tail[0].head
                assert import_type in ('multi_string', 'angle_string'), \
                    'unexpected child of import statement (stage 2 parser ' \
                    'inconsistent with grammar?)'

                if import_type == 'multi_string':
                    # Concatenate, stripping quotes.
                    import_content = ''.join(x.tail[0][1:-1]
                        for x in item.tail[0].tail)
                    if filename is None:
                        target = os.path.abspath(import_content)
                    else:
                        target = os.path.abspath(os.path.join(
                            os.path.dirname(filename), import_content))
                    if not os.path.exists(target):
                        target = None

                else:
                    import_content = item.tail[0].tail[0][1:-1] # ← strip angles
                    # The import should be resolved in the built-in context.
                    for prefix in self.importpath:
                        target = os.path.abspath(os.path.join(prefix,
                            import_content))
                        if os.path.exists(target):
                            break
                    else:
                        target = None

                if target is None:
                    # TODO: account for CPP-ing
                    item.calc_position()
                    raise ParseError('import \'%s\' not found' %
                        import_content, filename=filename,
                        lineno=item.min_line)

                if target in read:
                    continue

                more_source, more_ast_raw, r = self.parse1.parse_file(target)
                read |= r
                assert more_ast_raw.head == 'start', 'unexpected raw AST structure'
                more_ast_augmented = [(more_source, target, t) for t in more_ast_raw.tail]

                queue.extendleft(reversed(more_ast_augmented))

            else:
                final_ast_augmented.append((source, filename, item))

        return final_ast_augmented, read

    def parse_file(self, filename):
        source, ast_raw, read = self.parse1.parse_file(filename)
        return self._resolve(source, filename, ast_raw, read)

    def parse_string(self, string):
        source, ast_raw, read = self.parse1.parse_string(string)
        return self._resolve(source, None, ast_raw, read)
