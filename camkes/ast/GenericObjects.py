#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''
Objects that can appear in the derived AST that are common to both CAmkES IDL
and ADL. See accompanying docs for more information.
'''

class ASTObject(object):
    def __init__(self, filename=None, lineno=-1):
        self.filename = filename
        self.lineno = lineno

    def unresolved(self):
        '''Unresolved references rooted at this element.'''
        return reduce(lambda a, x: a.union(x.unresolved()), self.children(), set())

    @staticmethod
    def externally_resolved():
        '''Whether references to this type should be considered resolved even
        when they are not. Although this sounds like it makes no sense, this is
        actually the behaviour we want for types that are resolved to entities
        outside CAmkES. E.g. port types that typically reference C struct
        types.'''
        return False

    def children(self):
        '''Returns the contained descendents of this object. Override this
        function in types that have children.'''
        return []

    def collapse_references(self):
        pass

    def __eq__(self, other):
        '''Determine if two AST objects are identical. Used for deduping AST
        entries after parsing.'''
        # AST objects must at least have the same type.
        if type(self) != type(other):
            return False

        # Attributes to ignore in comparison.
        ignore = set(['filename', 'lineno'])

        attrs = set(self.__dict__.keys()).difference(ignore)
        other_attrs = set(other.__dict__.keys()).difference(ignore)
        if attrs != other_attrs:
            # The two objects have different attribute NAMES.
            return False
        for i in attrs:
            if getattr(self, i) != getattr(other, i):
                # The two objects have different attribute VALUES.
                return False

        return True

    def __ne__(self, other):
        '''I hate you, Python'''
        return not self == other

    def try_collapse(self, member):
        r = getattr(self, member)
        if isinstance(r, Reference) and r._referent is not None:
            setattr(self, member, r._referent)
        r = getattr(self, member)
        if not isinstance(r, Reference):
            r.collapse_references()

    def try_collapse_list(self, member):
        r = getattr(self, member)
        for i, j in enumerate(r):
            if isinstance(j, Reference) and j._referent is not None:
                r[i] = j._referent
            if not isinstance(r[i], Reference):
                r[i].collapse_references()

class Import(ASTObject):
    def __init__(self, source, relative=True, filename=None, lineno=-1):
        assert isinstance(source, str)
        super(Import, self).__init__(filename=filename, lineno=lineno)
        self.source = source
        self.relative = relative

    def __repr__(self):
        return 'import %(open)s%(source)s%(close)s;' % {
            'open':'"' if self.relative else '<',
            'source':self.source,
            'close':'"' if self.relative else '>',
        }

class Include(ASTObject):
    def __init__(self, source, relative=True, filename=None, lineno=-1):
        assert isinstance(source, str)
        super(Include, self).__init__(filename=filename, lineno=lineno)
        self.source = source
        self.relative = relative

    def __repr__(self):
        return 'include %(open)s%(source)s%(close)s;' % {
            'open':'"' if self.relative else '<',
            'source':self.source,
            'close':'"' if self.relative else '>',
        }

class Reference(ASTObject):
    '''This class encapsulates references to other entities that have been
    parsed. It can also be used to represent forward references in the input.
    '''
    def __init__(self, symbol, symbol_type, filename=None, lineno=-1):
        super(Reference, self).__init__(filename=filename, lineno=lineno)
        assert isinstance(symbol, str)
        self._symbol = symbol
        assert isinstance(symbol_type, type)
        self._type = symbol_type
        self._referent = None

    def unresolved(self):
        if not self._type.externally_resolved() and self._referent is None:
            return set([self])
        else:
            return super(Reference, self).unresolved()

    def children(self):
        # The referent's children if this reference is resolved.
        if self._referent:
            return self._referent.children()
        return []

    def collapse_references(self):
        raise Exception('Collapse references called on a reference itself')

    def resolve_to(self, obj):
        assert isinstance(obj, self._type)
        self._referent = obj

    def __repr__(self):
        # TODO: Can't do this branching until all objects are in one file.
        #if isinstance(self.symbol_type, Composition):
        #    return 'composition %(_symbol)s;' % self.__dict__
        #elif isinstance(self._symbol_type, Configuration):
        #    return 'configuration %(_symbol)s;' % self.__dict__
        #else:
        #    return self._symbol
        return self._symbol
