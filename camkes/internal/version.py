#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

# Versioning functionality

from memoization import memoized
import hashlib, os, re

@memoized
def version_hash():
    '''Computes a version identifier by hashing the current source code state.
    Values returned by this function are suitable for using as keys to the
    template cache.'''
    # Files to consider relevant. Each entry should be a pair of (path, filter)
    # where 'path' is relative to the directory of this file and 'filter' is a
    # regex describing which filenames to match under the given path.
    SOURCES = [
        ('../', r'^.*\.py$'),    # Python sources
        ('../templates', r'.*'), # Templates
    ]

    my_path = os.path.dirname(os.path.abspath(__file__))
    sources = set()

    # Accumulate all relevant source files.
    for s in SOURCES:
        path = os.path.join(my_path, s[0])
        regex = re.compile(s[1])
        for root, _, files in os.walk(path):
            for f in files:
                if regex.match(f):
                    sources.add(os.path.abspath(os.path.join(root, f)))

    # Hash each file and hash a concatenation of these hashes. Note, hashing a
    # hash is not good practice for cryptography, but it's fine for this
    # purpose.
    hfinal = hashlib.sha1() #pylint: disable=E1101
    for s in sources:
        with open(s, 'r') as f:
            h = hashlib.sha1(f.read()).hexdigest() #pylint: disable=E1101
        hfinal.update('%s|' % h) #pylint: disable=E1101
    return hfinal.hexdigest()

def version_number():
    '''Returns the current version number by reading the VERSION file in
    the top-level directory of this project.'''
    my_path = os.path.dirname(os.path.abspath(__file__))
    version_path = os.path.join(my_path, '../../VERSION')
    with open(version_path, 'r') as f:
        return f.read()
