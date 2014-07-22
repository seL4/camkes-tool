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
A collection of files and their contents. Usage should be fairly
self-explanatory.
'''

import copy, os
import hash

class FileSet(object):
    def __init__(self, files):
        self.files = {}
        self.output = None
        self.extend(files)

    def extend(self, more_files):
        for f in more_files:
            self.files[os.path.abspath(f)] = hash.file_hash(f)

    def valid(self):
        for path, ident in self.files.items():
            if not os.path.exists(path) or hash.file_hash(path) != ident:
                return False
        return True

    def specialise(self, output):
        '''Return a refined copy of this that is associated with a particular
        contents of some output file. In this way we can link a collection of
        inputs (self.files) to an output.'''
        c = copy.deepcopy(self)
        c.output = output
        return c

    def __repr__(self):
        return str(self.files)
