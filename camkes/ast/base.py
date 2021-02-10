#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

from camkes.internal.hash import camkes_hash
from .exception import ASTError
from .location import SourceLocation
from .traversal import NullContext, TraversalAction, TraversalContext
import abc, collections, six

class ASTObject(six.with_metaclass(abc.ABCMeta, object)):

    child_fields = ()

    # Fields that should be ignored when calculating an object hash or
    # performing comparisons. Inheriting classes should extend this if
    # necessary.
    no_hash = ('child_fields', '_frozen', '_location', 'no_hash', '_parent')

    def __init__(self, location=None):
        assert location is None or isinstance(location, SourceLocation)
        self._frozen = False
        self._location = location
        self._parent = None

    @property
    def frozen(self):
        return self._frozen
    @frozen.setter
    def frozen(self, value):
        assert isinstance(value, bool)
        if self._frozen and not value:
            raise TypeError('you cannot unfreeze an AST object')
        self._frozen = value

    @property
    def location(self):
        return self._location
    @location.setter
    def location(self, value):
        assert value is None or isinstance(value, SourceLocation)
        if self.frozen:
            raise TypeError('you cannot change the location of a frozen AST '
                'object')
        self._location = value

    @property
    def parent(self):
        return self._parent
    @parent.setter
    def parent(self, value):
        assert value is None or isinstance(value, ASTObject)
        if self.frozen:
            raise TypeError('you cannot change the parent of a frozen AST '
                'object')
        self._parent = value

    def freeze(self):
        if self.frozen:
            return
        for f in self.child_fields:
            assert hasattr(self, f)
            item = getattr(self, f)
            if isinstance(item, (list, tuple)):
                for i in item:
                    i.freeze()
            elif item is not None:
                item.freeze()
        self.frozen = True

    @property
    def filename(self):
        if self.location is None:
            return None
        return self.location.filename

    @property
    def lineno(self):
        if self.location is None:
            return None
        return self.location.lineno

    @property
    def children(self):
        '''Returns the contained descendents of this object.'''
        assert isinstance(self.child_fields, tuple), 'child_fields is not a ' \
            'tuple; accidentally declared as a string?'
        kids = []
        for f in self.child_fields:
            assert hasattr(self, f)
            item = getattr(self, f)
            if isinstance(item, (list, tuple)):
                kids.extend(item)
            else:
                kids.append(item)
        return kids

    def adopt(self, child):
        child.parent = self

    def claim_children(self):
        pass

    def __cmp__(self, other):
        if type(self) != type(other):
            return cmp(str(type(self)), str(type(other)))

        for f in (k for k in self.__dict__.keys() if k not in self.no_hash):
            if not hasattr(other, f):
                return 1
            elif getattr(self, f) is getattr(other, f):
                # PERF: Field `f` in both items references the exact same
                # object. Skip the remainder of this iteration of the loop to
                # avoid unnecessarily comparing an object with itself.
                continue
            elif getattr(self, f) != getattr(other, f):
                if type(getattr(self, f)) != type(getattr(other, f)):
                    return cmp(str(type(getattr(self, f))),
                        str(type(getattr(other, f))))
                elif isinstance(getattr(self, f), type):
                    assert isinstance(getattr(other, f), type), 'incorrect ' \
                        'control flow in __cmp__ (bug in AST base?)'
                    return cmp(str(getattr(self, f)), str(getattr(other, f)))
                return cmp(getattr(self, f), getattr(other, f))

        return 0

    def __hash__(self):
        return camkes_hash((k, v) for k, v in self.__dict__.items()
                if k not in self.no_hash)

    # When comparing `ASTObject`s, we always want to invoke
    # `ASTObject.__cmp__`, but unfortunately we inherit rich comparison methods
    # from `object`. Override these here, to force `ASTObject.__cmp__`. Note
    # that you cannot call `cmp` in any of the following functions or they will
    # infinitely recurse.
    def __lt__(self, other):
        return self.__cmp__(other) < 0
    def __le__(self, other):
        return self.__cmp__(other) <= 0
    def __eq__(self, other):
        return self.__cmp__(other) == 0
    def __ne__(self, other):
        return self.__cmp__(other) != 0
    def __gt__(self, other):
        return self.__cmp__(other) > 0
    def __ge__(self, other):
        return self.__cmp__(other) >= 0

    def preorder(self, f, context=None):
        '''
        Pre-order traversal. Note that, unlike the post-order traversal below,
        this does *not* recurse into the children of nodes you replace. The
        rationale for this is that there is no other way to indicate to the
        traversal algorithm that you do not wish to recurse into the children
        and, if you *do* want to recurse, you can accomplish this manually
        yourself before returning the replacement.
        '''
        assert isinstance(f, TraversalAction)
        assert context is None or isinstance(context, TraversalContext)
        assert isinstance(self.child_fields, tuple), 'child_fields is not a ' \
            'tuple; accidentally declared as a string?'
        if context is None:
            context = NullContext()
        for field in self.child_fields:
            assert hasattr(self, field)
            item = getattr(self, field)
            if isinstance(item, (list, tuple)):
                for i in six.moves.range(len(item)):
                    replacement = f(item[i])
                    if replacement is item[i]:
                        with context(f):
                            replacement.preorder(f, context)
                    else:
                        getattr(self, field)[i] = replacement
            else:
                replacement = f(item)
                if replacement is item and replacement is not None:
                    with context(f):
                        replacement.preorder(f, context)
                elif replacement is not item:
                    setattr(self, field, replacement)

    def postorder(self, f, context=None):
        assert isinstance(f, TraversalAction)
        assert context is None or isinstance(context, TraversalContext)
        assert isinstance(self.child_fields, tuple), 'child_fields is not a ' \
            'tuple; accidentally declared as a string?'
        if context is None:
            context = NullContext()
        for field in self.child_fields:
            assert hasattr(self, field)
            item = getattr(self, field)
            if isinstance(item, (list, tuple)):
                for i in six.moves.range(len(item)):
                    with context(f):
                        item[i].postorder(f, context)
                    replacement = f(item[i])
                    if replacement is not item[i]:
                        getattr(self, field)[i] = replacement
            else:
                if item is not None:
                    with context(f):
                        item.postorder(f, context)
                replacement = f(item)
                if replacement is not item:
                    setattr(self, field, replacement)

    def label(self):
        return None

class MapLike(six.with_metaclass(abc.ABCMeta, ASTObject, collections.Mapping)):

    no_hash = ASTObject.no_hash + ('_mapping',)

    def __init__(self, location=None):
        super(MapLike, self).__init__(location)
        self._mapping = None

    def freeze(self):
        if self.frozen:
            return
        super(MapLike, self).freeze()
        self._mapping = {}
        def add(d, i):
            duplicate = d.get(i.name)
            if duplicate is not None:
                raise ASTError('duplicate entity \'%s\' defined, '
                    'collides with %s at %s:%s' % (i.name,
                    type(duplicate).__name__, duplicate.filename,
                    duplicate.lineno), i)
            d[i.name] = i
        for field in self.child_fields:
            assert hasattr(self, field)
            item = getattr(self, field)
            if isinstance(item, (list, tuple)):
                [add(self._mapping, x) for x in item
                    if hasattr(x, 'name') and x.name is not None]
            elif item is not None and hasattr(item, 'name') and \
                    item.name is not None:
                add(self._mapping, item)

    def __getitem__(self, key):
        assert self.frozen, 'dict access on non-frozen object'
        return self._mapping[key]
    def __iter__(self):
        assert self.frozen, 'dict access on non-frozen object'
        return iter(self._mapping)
    def __len__(self):
        assert self.frozen, 'dict access on non-frozen object'
        return len(self._mapping)
