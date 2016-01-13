#!/usr/bin/env python
# -*- coding: utf-8 -*-

#
# Copyright 2015, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''
Stage 8 parser. The following parser is designed to accept a stage 7 parser,
whose output it consumes. This parser's purpose is to resolve settings that
reference other attributes.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

from camkes.ast import Attribute
from .base import Transformer
from .exception import ParseError
import collections

# Re-use the post-condition of the stage 6 parser as our pre-condition; that
# only a single assembly remains.
from .stage6 import postcondition as precondition

def postcondition(ast_lifted):
    '''
    All settings are resolved.
    '''
    return all(not isinstance(x.value, Attribute) for x in
        ast_lifted.assembly.configuration.settings)

def resolve(ast_lifted):
    '''
    Resolve all attribute references to concrete values.

    There's not a lot of type safety in this resolution process because the
    attributes themselves inherently aren't strongly typed. We try and do what
    we can by detecting the source and destination type when the attribute(s)
    are declared and ensuring they match.
    '''
    to_resolve = []
    values = collections.defaultdict(dict)

    assembly = ast_lifted.assembly

    for s in assembly.configuration.settings:
        if isinstance(s.value, Attribute):
            to_resolve.append(s)
        else:
            values[s.instance][s.attribute] = s.value

    for r in to_resolve:
        # Find the prefix of the instance of this attribute. The idea here is
        # that we have two settings:
        #   foo.bar.baz = 2;
        #   foo.bar.moo.cow <- baz;
        # We know that the prefix of the reference's instance is the instance
        # of the referent. In the above, the prefix of `foo.bar.moo.cow` is
        # `foo.bar`, that matches the instance of the first setting, `foo.bar`.
        assert '.' in r.instance, 'illegal attribute reference'
        name = '.'.join(r.instance.split('.')[:-1])

        attribute = r.value.name

        # Do some type checking if we can. This is only possible if the
        # reference and referent attribute have been declared with a type.
        source_type = r.value.type
        try:
            destination_type = [a for a in
                [x for x in
                    assembly.composition.instances
                    if x.name == s.instance][0].type.attributes
                if a.name == s.attribute][0].type
            if destination_type != source_type:
                raise ParseError('mismatched types in attribute reference',
                    r.filename, r.lineno)
        except IndexError:
            pass

        # Resolve the reference.
        try:
            r.value = values[name][attribute]
        except KeyError:
            raise ParseError('reference to attribute %s which is unset' %
                r.value.name, r.filename, r.lineno)

class Parse8(Transformer):
    def precondition(self, ast_lifted, _):
        return precondition(ast_lifted)

    def postcondition(self, ast_lifted, _):
        return postcondition(ast_lifted)

    def transform(self, ast_lifted, read):
        resolve(ast_lifted)
        return ast_lifted, read
