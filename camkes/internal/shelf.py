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
A limited reimplementation of Python's shelve module.

To give a bit of the back story as to why this exists, when you're really
hammering a Python shelve it has a tendency to corrupt the underlying database.
I haven't diagnosed the exact cause of this, but there are a series of related
open Python bugs that basically fob the problem off on the backing store,
Berkeley DB.

This module uses SQLite as its backing store. SQLite has quite bold claims of
resilience and robustness, and hammering one of these in the same pattern does
not produce the corruption observed with shelve. Note that high write
contention on one of these may still cause failures (with a "database locked"
error), but your database integrity is preserved at least.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

import collections, os, six, sqlite3, tempfile
from .memoization import memoize

class Shelf(collections.MutableMapping):
    def __init__(self, path):
        if not os.path.exists(path):
            with open(path, 'wb') as f:
                f.write(blank_database())
        self.db = sqlite3.connect(path)

    def __delitem__(self, key):
        assert isinstance(key, six.string_types)

        with self.db:
            c = self.db.cursor()
            c.execute('delete from data where key=?;', (key,))
            if c.rowcount == 0:
                raise KeyError(key)

    def __getitem__(self, key):
        assert isinstance(key, six.string_types)

        c = self.db.cursor()
        c.execute('select value from data where key=?;', (key,))
        try:
            return c.fetchone()[0]
        except TypeError:
            raise KeyError(key)

    def __iter__(self):
        for (key,) in self.db.execute('select key from data;'):
            yield key

    def __len__(self):
        for (size,) in self.db.execute('select count(*) from data;'):
            return size

    def __setitem__(self, key, value):
        assert isinstance(key, six.string_types)
        assert isinstance(value, six.string_types)

        with self.db:
            self.db.execute('delete from data where key=?;', (key,))
            self.db.execute('insert into data (key, value) values (?, ?);',
                (key, value))

@memoize()
def blank_database():
    '''
    Return data representing a blank database as a bytearray.

    See the note on the identically named function in cachea.py for the
    motivation for this function.
    '''
    _, tmp = tempfile.mkstemp()

    conn = sqlite3.connect(tmp)
    with conn:
        conn.execute('''
            create table if not exists data (
                key text primary key not null,
                value text not null);''')
    conn.close()

    data = open(tmp, 'rb').read()
    os.remove(tmp)

    return data
