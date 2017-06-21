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
Level A cache.

This cache is designed to store executions, where an execution consists of:

 1. Command line arguments;
 2. Current working directory;
 3. All input files; and
 4. Output file.

The cache is hosted in a root directory specified by the caller on creation.
This directory contains the following:

    root
     ├ dbs/
     │  ├ <args SHA256 hash>
     │  ├ <args SHA256 hash>
     │  ├ <args SHA256 hash>
     │  │  ├ <cwd SHA256 hash>
     │  │  ├ <cwd SHA256 hash>
     │  │  ├ <cwd SHA256 hash>
     │  │  │  └ cache.db   - metadata related to executions
     │  │  └ ...
     │  └ ...
     └ data/      - file data named by SHA256 hashes

Only two basic operations are supported: `load` and `save`. Callers are
expected to call `load` when looking for a previously cached execution, and
provide their command line arguments and current working directory. On a cache
hit, the previously saved output is returned as a string. On a cache miss,
`None` is returned. Callers are expected to call `save` when they want to note
a successful execution for later retrieval. They are expected to provide
command line arguments, current working directory, the output data as a string
and input data in a previously primed form (discussed below). Expected usage is
roughly:

    c = Cache('/my/cache/root')
    result = c.load(sys.argv[1:], os.getcwd())

    if result is not None:
        # Cache hit
        return result

    else:
        # Cache miss
        output, my_read_files = long_running_calculation()

        # Save the calculation for next time
        inputs = prime_inputs(my_read_files)
        c.save(sys.argv[1:], os.getcwd(), output, inputs)
        c.flush()

        return output

Setting up inputs is separated into its own manual step because the common case
within CAmkES involves caching many things with the same set of inputs. It
would be unnecessarily costly to repeatedly hash the same files.

To explain why SQLite serves as the backing store for this cache rather than
something simpler like pickle or shelve, an anticipated use case is for this
cache to be accessed by external tools. Storing data in a structured, language-
independent format allows these tools to be written in languages other than
Python.

A possibly surprising implementation detail is that cache entries are initially
buffered in memory and only written to the backing store on a call to `flush`.
The motivation for this is not satisfying following `load` requests from
memory, but rather coalescing database updates. In initial tests with parallel
CAmkES invocations, it was discovered that fine grained database updates caused
high enough write contention on the database to stall builds and eventually
timeout database actions. This similarly motivates the extra levels of
directory hierarchy in the cache structure. By having per-args, per-cwd
databases, writes are less likely to be contended and we get better I/O
throughput.

Note that, although the design of this cache has been motivated by CAmkES,
nothing in this file is intrinsically CAmkES specific.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

import collections, os, six, sqlite3, tempfile
from .cache import Cache as Base
from .flatten_args import flatten_args
from .mkdirp import mkdirp
from .memoization import memoize
from .strhash import hash_string

MY_DIR = os.path.dirname(os.path.abspath(__file__))

CREATE_OUTPUT = open(os.path.join(MY_DIR, 'create_output.sql'), 'rt').read()
CREATE_INPUT = open(os.path.join(MY_DIR, 'create_input.sql'), 'rt').read()
INSERT_OUTPUT = open(os.path.join(MY_DIR, 'insert_output.sql'), 'rt').read()
INSERT_INPUT = open(os.path.join(MY_DIR, 'insert_input.sql'), 'rt').read()
SELECT_OUTPUT = open(os.path.join(MY_DIR, 'select_output.sql'), 'rt').read()
SELECT_INPUTS = open(os.path.join(MY_DIR, 'select_inputs.sql'), 'rt').read()
DELETE_OUTPUT = open(os.path.join(MY_DIR, 'delete_output.sql'), 'rt').read()
DELETE_INPUTS = open(os.path.join(MY_DIR, 'delete_inputs.sql'), 'rt').read()

def hash_file(filename):
    with open(filename, 'rb') as f:
        return hash_string(f.read())

def prime_inputs(paths):
    '''
    Setup some inputs for later use in a call to `save`.
    '''
    return tuple((p, hash_file(p)) for p in paths)

class Cache(Base):
    def __init__(self, root):
        self.root = root
        self.data = os.path.abspath(os.path.join(root, 'data'))
        mkdirp(self.data)

        # In-memory cache of written entries. We write these back to the
        # underlying database when `flush` is called.
        self.pending = {}

    def flush(self):
        for (args, cwd), (sha256, inputs) in self.pending.items():

            conn = self._open_db(args, cwd)
            with conn:
                c = conn.cursor()

                # Remove any previous record.
                c.execute(SELECT_OUTPUT, (args, cwd))
                try:
                    id, _ = c.fetchone()
                except TypeError:
                    pass
                else:
                    c.execute(DELETE_INPUTS, (id,))
                    c.execute(DELETE_OUTPUT, (id,))

                # Save the output record.
                c.execute(INSERT_OUTPUT, (args, cwd, sha256))

                # Save the input records.
                assert c.lastrowid is not None, 'no row ID provided on ' \
                    'insertion to output table (bug in level A cache table ' \
                    'schema?)'
                fk = c.lastrowid
                c.executemany(INSERT_INPUT, ((fk, p, h) for p, h in inputs))

        self.pending = {}

    def load(self, argv, cwd):
        assert isinstance(argv, collections.Iterable) and \
            all(isinstance(x, six.string_types) for x in argv)
        assert isinstance(cwd, six.string_types)

        args = flatten_args(argv)

        try:
            # First try retrieving from our in-memory cache.
            sha256, inputs = self.pending[(args, cwd)]
        except KeyError:
            # If that missed, look in the database.
            conn = self._open_db(args, cwd)
            with conn:
                # Locate the output record.
                c = conn.cursor()
                c.execute(SELECT_OUTPUT, (args, cwd))
                try:
                    id, sha256 = c.fetchone()
                except TypeError:
                    # Cache miss.
                    return None
                assert c.fetchone() is None, 'multiple cached values for a single ' \
                    'set of inputs (bug in level A cache?)'

                inputs = c.execute(SELECT_INPUTS, (id,)).fetchall()

        # Check the inputs are identical to when we saved this record.
        for path, sig in inputs:
            if not os.path.isabs(path):
                path = os.path.join(cwd, path)
            if not os.path.exists(path) or sig != hash_file(path):
                # Mismatch (== cache miss).
                return None

        with open(os.path.join(self.data, sha256), 'rt') as f:
            return f.read()

    def _open_db(self, args, cwd):
        assert isinstance(args, six.string_types)
        assert isinstance(cwd, six.string_types)

        dirname = os.path.join(self.root, 'dbs', hash_string(args),
            hash_string(cwd))
        mkdirp(dirname)

        db = os.path.join(dirname, 'cache.db')

        if not os.path.exists(db):
            with open(db, 'wb') as f:
                f.write(blank_database())

        conn = sqlite3.connect(db)

        return conn

    def save(self, argv, cwd, output, inputs):
        assert isinstance(argv, collections.Iterable) and \
            all(isinstance(x, six.string_types) for x in argv)
        assert isinstance(cwd, six.string_types)
        assert isinstance(output, six.string_types)
        assert isinstance(inputs, collections.Iterable)

        args = flatten_args(argv)

        # Save the output itself.
        sha256 = hash_string(output)
        output_path = os.path.join(self.data, sha256)
        with open(output_path, 'wt') as f:
            f.write(output)

        # Save the metadata in the in-memory cache.
        self.pending[(args, cwd)] = (sha256, inputs)

@memoize()
def blank_database():
    '''
    Return data representing a blank database as a bytearray.

    One of the surprising things when profiling the original implementation of
    this cache was that a hot spot was creating SQLite databases. The SQLite
    CREATE operation is not particularly efficient, because it is assumed that
    you will not be executing it often. However, we are. This memoized function
    minimises the cost of repeated database creation, cutting build time to 20%
    in a representative project.
    '''
    _, tmp = tempfile.mkstemp()

    conn = sqlite3.connect(tmp)
    with conn:
        conn.execute(CREATE_OUTPUT)
        conn.execute(CREATE_INPUT)
    conn.close()

    data = open(tmp, 'rb').read()
    os.remove(tmp)

    return data
