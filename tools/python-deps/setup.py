#!/usr/bin/env python
# Copyright 2017, Data 61
# Commonwealth Scientific and Industrial Research Organisation (CSIRO)
# ABN 41 687 119 230.
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(DATA61_BSD)
#

"""
Setup script for dependency metapackage.

To add a python dependency, add it to the DEPS list below.

To publish to pypitest:
python setup.py sdist upload -r pypitest

To publish to pypi:
python setup.py sdist upload -r pypi
"""

from setuptools import setup

DEPS = [
    'jinja2',
    'orderedset',
    'plyplus',
    'pyelftools',
    'sel4-deps',
    'pycparser',
]

setup(
    name='camkes-deps',
    version='0.2.0',
    description='Metapackage for downloading build dependencies for CAmkES',
    url='https://wiki.sel4.systems/CAmkES',
    licence='BSD2',
    author='TrustworthySystems',
    author_email='Stephen.Sherratt@data61.csiro.au',
    install_requires=DEPS,
)
