#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''Various helpers for doing advanced things with dictionaries.'''

import itertools

def safe(f, *args, **kwargs):
    '''Take an arbitrary function that returns a bool and force it to return
    False if it hits an exception.'''
    try:
        return f(*args, **kwargs)
    except:
        return False

def get_fields(s):
    '''Return a set of field names referenced as formatting keys in the given
    string. I thought there would be an easier way to get this, but I can't
    find one. E.g. get_fields('%(hello)s %(world)s') returns
    set('hello', 'world').'''
    class FakeDict(dict):
        def __init__(self):
            super(FakeDict, self).__init__()
            self.referenced = set()
        def __getitem__(self, key):
            self.referenced.add(key)
            return ''
    f = FakeDict()
    s % f # Value deliberately discarded
    return f.referenced

class Key(object):
    '''A jazzed up string to use as a dict key. The idea is to use with an
    optional guard that determines whether the key you're looking up really is
    a match. Look at the use in Template.py for example usage.'''
    def __init__(self, key, guard=None):
        self.key = key
        self.guard = guard or (lambda x: True)

    def specialise(self, spec_dict):
        return Key(self.key % spec_dict, self.guard)

    def matches(self, key, entity):
        return self.key == key and (not self.guard or safe(self.guard, entity))

    def get_fields(self):
        return get_fields(self.key)

def combinations(d):
    '''Don't be scared by the following line. This function takes a dict whose
    values are lists and generates all possible dicts whose keys are the
    original dict's keys and values are elements that reside in the list value
    associated with the key in the original dict. E.g.
    combinations({'hello':[1, 2], 'world':[3, 4]}) returns a generator yielding
    [{'hello':1, 'world':3}, {'hello':1, 'world':4}, {'hello':2, 'world':3},
    {'hello':2, 'world':4}].'''
    return itertools.imap(lambda x: dict(x),
        itertools.product(*map(lambda x: map(lambda y: (x[0], y), x[1]),
            d.items())))
