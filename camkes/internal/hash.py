#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

import hashlib

def content_hash(data):
    return hashlib.sha1(data).hexdigest() #pylint: disable=E1101

def file_hash(filename):
    with open(filename, 'r') as f:
        return content_hash(f.read())
