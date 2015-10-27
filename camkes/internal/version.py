#!/usr/bin/env python
# -*- coding: utf-8 -*-

# Copyright 2015, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''Versioning functionality. This computes a version identifier based on the
current source code state. It was decided this was more reliable while the tool
is under active development. Note that any extraneous files in your source
directory that match the version filters will be accumulated in the version
computation.'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

from .memoization import memoize
import hashlib, os, re, six

@memoize()
def sources():
    '''
    Yield absolute paths to the sources of CAmkES itself, along with their
    SHA256 hash.
    '''

    # Accumulate sources to return. Ordinarily we would implement this function
    # as a generator, but then we couldn't memoize it.
    result = []

    # Files to count as "CAmkES sources."
    include = [re.compile(x) for x in
        (r'^camkes\.sh$', r'^camkes/ast/[^/]*\.py$',
        r'^camkes/internal/[^/]*\.(py|sql)$', r'^camkes/parser/[^/]*\.py$',
        r'^camkes/runner/[^/]*\.py$', r'^camkes/templates/.*$')]

    # Directory from which the above paths are relevant.
    root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))

    for base, _, files in os.walk(root):
        for f in files:
            if f.endswith('.swp'):
                # Skip vim swap files.
                continue
            abspath = os.path.join(base, f)
            path = os.path.relpath(abspath, root)
            for inc in include:
                if inc.match(path) is not None:
                    content = open(abspath, 'rb').read()
                    result.append((abspath, hashlib.sha256(content).hexdigest()))
                    break

    return result

@memoize()
def version():
    # Accumulate all relevant source files.
    srcs = sorted(sources())

    # Hash each file and hash a concatenation of these hashes. Note, hashing a
    # hash is not good practice for cryptography, but it's fine for this
    # purpose.
    hfinal = hashlib.sha256()
    for _, digest in srcs:
        chunk = '%s|' % digest
        if isinstance(chunk, six.text_type):
            chunk = chunk.encode('utf-8')
        hfinal.update(chunk)
    return hfinal.hexdigest()
