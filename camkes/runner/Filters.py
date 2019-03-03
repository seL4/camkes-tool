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

"""Filters to be applied to generated CapDL."""
from __future__ import absolute_import, division, print_function, \
    unicode_literals

import os, six, subprocess
from capdl import Cap, CNode, TCB, SC, lookup_architecture
from .NameMangling import Perspective


CAPDL_FILTERS = []
