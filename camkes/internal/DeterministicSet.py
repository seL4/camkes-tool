#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

class DeterministicSet(list):
    '''A replica of the native Python set type, designed to be deterministic in
    the order in which it returns its contents. Python's set type has the
    unfortunate property that contained elements are ordered (in the context of
    iteration) based on their hash. For certain types (e.g. str) hash is not
    guaranteed to be stable across executions (see the last note about __hash__
    at http://docs.python.org/dev/reference/datamodel.html#object.__hash__).
    The effect of this is that, when we use a set in a template, the template
    can be rendered differently across different executions of the runner. This
    is undesirable for many reasons.

    Note that only the bare minimum functions we need are implemented below. To
    make this more complete, the remaining set functions should be implemented
    and any dangerous underlying list functions should be masked.'''

    def __init__(self, iterable=None):
        unique = []
        for i in iterable or []:
            if i not in unique:
                unique.append(i)
        super(DeterministicSet, self).__init__(unique)

    def add(self, elem):
        if elem not in self:
            self.append(elem)

    def union(self, *others):
        for o in others:
            for i in o:
                if i not in self:
                    self.append(i)
