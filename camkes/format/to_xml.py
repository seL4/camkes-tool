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
Support for converting a CAmkES AST into XML.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

from camkes.ast import ASTObject
import numbers, six
import xml.etree.cElementTree as ET

def to_element(node):
    '''
    Convert an AST node to an XML element.
    '''

    elem = ET.Element(node.__class__.__name__)

    for field, value in ((k, v) for (k, v) in node.__dict__.items()
            if k not in node.no_hash):

        # Many ASTObjects have fields that are wrapped in @property and friends
        # to give some greater type safety. In this case, the underlying field
        # itself will be named with a leading prefix by convention. Strip these
        # in the XML output to avoid confusing the reader.
        if field.startswith('_'):
            field = field[1:]

        if isinstance(value, six.string_types + (numbers.Number,)):
            # Write primitive types directly.
            elem.set(field, str(value))

        elif isinstance(value, (list, tuple)):
            # Write lists of things contained in a subelement.
            subelem = ET.SubElement(elem, field)
            for v in value:
                if isinstance(v, six.string_types + (numbers.Number,)):
                    ET.SubElement(subelem, 'string', {'value':str(v)})
                elif isinstance(v, ASTObject):
                    subelem.append(to_element(v))
                elif v is None:
                    pass
                else:
                    raise NotImplementedError

        elif isinstance(value, ASTObject):
            elem.append(to_element(value))

        elif value is None:
            pass

        else:
            raise NotImplementedError

    return elem

def to_xml(ast):
    '''
    Translate an AST to a string of XML.
    '''
    root = ET.Element('root')
    for node in ast:
        if node is not None:
            root.append(to_element(node))
    return ET.tostring(root, encoding='utf-8')
