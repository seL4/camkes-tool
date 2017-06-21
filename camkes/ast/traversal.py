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
Context types for use with `ASTObject.postorder`.

Traversal of an AST with `postorder`, accepts an optional context that receives
enter and exit events each time a level of the AST is descended or ascended,
respectively. See its usage in `postorder` for the exact way in which it is
called. Any contexts provided by callers should be a descendent of
`TraversalContext`.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

import abc, six

class TraversalAction(six.with_metaclass(abc.ABCMeta, object)):
    '''
    Generic traversal action.
    '''

    @abc.abstractmethod
    def __call__(self, item):
        raise NotImplementedError

class TraversalContext(six.with_metaclass(abc.ABCMeta, object)):
    '''
    Generic AST traversal context.
    '''

    @abc.abstractmethod
    def __enter__(self):
        raise NotImplementedError

    @abc.abstractmethod
    def __exit__(self, type, value, traceback):
        raise NotImplementedError

    @abc.abstractmethod
    def __call__(self, f):
        assert isinstance(f, TraversalAction)
        raise NotImplementedError

class SimpleTraversalContext(six.with_metaclass(abc.ABCMeta, TraversalContext)):
    '''
    A traversal context that does not need to interact with the traversal
    action.
    '''

    def __call__(self, _):
        return self

class NullContext(SimpleTraversalContext):
    '''
    The default context if none is provided by the caller.
    '''

    def __enter__(self):
        pass

    def __exit__(self, *_):
        pass
