#!/usr/bin/env python
#
# Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
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
    'aenum',
    'jinja2',
    'orderedset',
    'plyplus',
    'pyelftools',
    'sel4-deps',
    'pycparser',
    'pyfdt',
    'concurrencytest',
    'simpleeval',

    # capDL deps
    'sortedcontainers',
    'hypothesis',
]

setup(
    name='camkes-deps',
    version='0.7.1',
    description='Metapackage for downloading build dependencies for CAmkES',
    url='https://docs.sel4.systems/CAmkES/',
    license='BSD2',
    author='TrustworthySystems',
    author_email='Stephen.Sherratt@data61.csiro.au',
    install_requires=DEPS,
)
