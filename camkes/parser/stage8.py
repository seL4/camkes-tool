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
Stage 8 parser. The following parser is designed to accept a stage 7 parser,
whose output it consumes. This parser's purpose is to resolve settings that
reference other attributes.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

from camkes.ast import AttributeReference
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
    return all(not isinstance(x.value, AttributeReference) for x in
        ast_lifted.assembly.configuration.settings)

def resolve(ast_lifted):
    '''
    Recursively resolve all setting references to concrete values.

    There's not a lot of type safety in this resolution process because the
    attributes themselves inherently aren't strongly typed. We rely on the type
    checking done when freeze is called on an assembly.
    '''
    to_resolve = []

    assembly = ast_lifted.assembly
    new_settings = []
    for s in assembly.configuration.settings:
        if isinstance(s.value, AttributeReference):
            to_resolve.append(s)
        else:
            new_settings.append(s)

    def sub_resolve(setting, depth):
        '''
        Recursive function for resolving setting references.  If a setting
        is a reference to another setting we try and resolve the next one (depth first).  If there
        is a circular reference we error out.  If any setting doesn't have
        a setting to resolve to, but has a default attribute value we use that.
        If there is no default and no setting then we 'forget' the alias so that we
        can fall back to defaults that other attributes have.  An attribute that doesn't
        get a setting or a default will not generate a symbol in the generated template.
        Thus if the attribute requires a setting the code compiler should generate an error later.
        '''

        if setting.value.reference in depth:
            errstring = ""
            for value in depth:
                errstring += value + "<-"
            raise ParseError('Loop detected in attribute references: %s<-...'
                    % (errstring+setting.value.reference), setting.location)
        # TODO Refactor AttributeReference to handle namespacing better than a
        # string containing '.' characters.
        instance_name, attribute_name = setting.value.reference.rsplit('.', 1)
        referents = [x for x in assembly.configuration.settings
            if x.instance == instance_name and
                x.attribute == attribute_name]
        if len(referents) == 0:
            # No existing settings for the attribute that our current attribute
            # refers to.  Check if it has a default value and use that.
            attribute = assembly.get_attribute(instance_name, attribute_name)
            if attribute is not None and attribute.default is not None:
                setting.value = attribute.default
                return True

            # If we didn't find a default, then try and use our own default if we have one
            attribute = assembly.get_attribute(setting.instance, setting.attribute)
            if attribute is not None and attribute.default is not None:
                setting.value = attribute.default
                return True

            setting.value = None
            return False

        elif len(referents) > 1:
            raise ParseError('setting refers to an attribute that '
                'is set multiple times', setting.location)

        if isinstance(referents[0].value, AttributeReference):
            if not sub_resolve(referents[0], depth +  [setting.value.reference]):
                setting.value = None
                return False

        setting.value = referents[0].value
        return True

    # Iterate through each setting we need to resolve
    for setting in to_resolve:
        if isinstance(setting.value, AttributeReference):
            if sub_resolve(setting, []):
                new_settings.append(setting)
        elif setting.value != None:
            # Already resolved
            new_settings.append(setting)

    assembly.configuration.settings = new_settings
    assembly.claim_children()

class Parse8(Transformer):
    def precondition(self, ast_lifted, _):
        return precondition(ast_lifted)

    def postcondition(self, ast_lifted, _):
        return postcondition(ast_lifted)

    def transform(self, ast_lifted, read):
        resolve(ast_lifted)
        return ast_lifted, read
