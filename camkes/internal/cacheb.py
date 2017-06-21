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
Level B cache.

This cache is designed to store executions, where an execution consists of:

 1. AST;
 2. Command line arguments;
 3. Extra input files (ELFs); and
 4. Output file.

It is designed to be a fallback cache when the level A cache misses. The cache
is hosted in a root directory specified by the caller on creation. This
directory contains the following:

    root
     ├ dbs/
     │  ├ <args SHA256 hash>
     │  ├ <args SHA256 hash>
     │  ├ <args SHA256 hash>
     │  │  └ cache.db   - metadata related to executions
     │  └ ...
     └ data/      - file data named by SHA256 hashes

The same two base operations as the level A cache are supported, `load` and
`save`, but they take different arguments. Callers are expected to pass to
`load` a prepared hash of the AST, their current list of command line
arguments, and a list of paths to ELF files. They are expected to provide the
same along with an output value when calling `save`. Expected usage is roughly:

    c = Cache('/my/cache/root')
    hashed_ast = prime_ast_hash(ast)
    result = c.load(hashed_ast, sys.argv[1:], my_elfs)

    if result is not None:
        # Cache hit
        return result

    else:
        # Cache miss
        output = long_running_calculation()

        # Save the calculation for next time
        c.save(hashed_ast, sys.argv[1:], my_elfs, output)
        c.flush()

        return output

As with the level A cache, the AST hash is a separate, manual step because it
is anticipated that callers may be trying to save many outputs with the same
AST and we would like to avoid repeatedly calculating the hash. The same
comments as for the level A cache also apply to motivate the in-memory
buffering and directory hierarchy.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

import os, six
from .cache import Cache as Base
from .filehash import hash_file
from .flatten_args import flatten_args
from .mkdirp import mkdirp
from .shelf import Shelf
from .strhash import hash_string

def make_key(primed, argv, inputs):
    return '%d|%s|%s' % (primed, hash_string(flatten_args(argv)),
        '|'.join('%s|%s' % (x, hash_file(x)) for x in sorted(inputs)))

def prime_ast_hash(ast):
    return hash(ast)

class Cache(Base):
    def __init__(self, root):
        self.root = root
        self.data = os.path.join(root, 'data')
        mkdirp(self.data)
        # In-memory cache of written entries. We write these back to the
        # underlying database when `flush` is called.
        self.pending = {}

    def flush(self):
        for (args, key), value in self.pending.items():
            shelf = self._open_shelf(args)
            shelf[key] = value
        self.pending = {}

    def load(self, primed_ast, argv, inputs):
        args = flatten_args(argv)

        try:
            key = make_key(primed_ast, argv, inputs)
        except IOError:
            # An input didn't exist or was inaccessible.
            return None
        try:
            # First try the in-memory cache.
            value = self.pending[(args, key)]
        except KeyError:
            try:
                # If that missed, look in the database.
                shelf = self._open_shelf(args)
                value = shelf[key]
            except KeyError:
                # Cache miss.
                return None

        with open(os.path.join(self.data, value), 'rt') as f:
            return f.read()

    def _open_shelf(self, args):
        assert isinstance(args, six.string_types)

        dirname = os.path.join(self.root, 'dbs', hash_string(args))
        mkdirp(dirname)

        shelf = Shelf(os.path.join(dirname, 'cache.db'))
        return shelf

    def save(self, primed_ast, argv, inputs, output):
        key = make_key(primed_ast, argv, inputs)
        args = flatten_args(argv)
        value = hash_string(output)
        with open(os.path.join(self.data, value), 'wt') as f:
            f.write(output)
        self.pending[(args, key)] = value
