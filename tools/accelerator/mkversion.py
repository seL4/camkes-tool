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

import os, sys

sys.path.append(os.path.join(os.path.dirname(__file__), '../..'))
from camkes.internal.version import version

sys.stdout.write('''
#ifndef VERSION_H_
#define VERSION_H_

/* This file is generated; do not edit */

#define VERSION "%s"

#endif
'''.strip() % version())
