#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''Compilation caching infrastructure for the code generator. Nothing in here
is actually CAmkES-specific.'''

import hash, os, cPickle

class Cache(object):
    def __init__(self, root):
        self.root = root

    def get_file(self, key):
        def resolve(key):
            assert isinstance(key, list)
            assert len(key) > 0
            h = hash.content_hash(repr(key[0]))
            if len(key) > 1:
                r = resolve(key[1:])
                h = os.path.join(h, r)
            return h
        return os.path.join(self.root, resolve(key))

    def __setitem__(self, key, value):
        path = self.get_file(key)
        dirname = os.path.dirname(path)
        if not os.path.exists(dirname):
            os.makedirs(dirname)
        with open(path, 'w') as f:
            cPickle.dump(value, f)

    def _get(self, path):
        with open(path, 'r') as f:
            return cPickle.load(f)

    def __getitem__(self, key):
        path = self.get_file(key)
        return self._get(path)

    def get(self, key, default=None):
        path = self.get_file(key)
        if os.path.exists(path):
            return self._get(path)
        return default

    def __contains__(self, key):
        path = self.get_file(key)
        return os.path.exists(path)
