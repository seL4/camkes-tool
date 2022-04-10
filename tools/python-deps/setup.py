#!/usr/bin/env python
#
# Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

"""
Setup script for dependency metapackage.

To add a python dependency, add it to the DEPS list below.

To publish using these instructions, you need the virtualenv package 
installed, and a properly set up ~/.pypirc file.

To publish to pypitest:
python3 -m build
twine upload -r testpypi dist/*

To publish to pypi:
python3 -m build
twine upload -r pypi dist/*

"""

from setuptools import setup

DEPS = [
    'aenum',
    'jinja2',
    'ordered-set',
    'orderedset', # For older source trees: remove in 0.7.3
    'plyplus',
    'pyelftools',
    'sel4-deps',
    'pycparser',
    'pyfdt',
    'concurrencytest',
    # capDL deps
    'sortedcontainers',
    'hypothesis',
]

setup(
    name='camkes-deps',
    version='0.7.2',
    description='Metapackage for downloading build dependencies for CAmkES',
    long_description = """
The CAmkES tool has many python dependencies.  This package depends on them all
so that installing this package will pull in all the necessary packages.

This package is maintained as part of https://github.com/seL4/camkes-tool.git, 
in directory https://github.com/seL4/camkes-tool/tree/master/tools/python-deps
""",
    long_description_content_type = "text/markdown",
    url='https://docs.sel4.systems/CAmkES/',
    license='BSD2',
    author='TrustworthySystems',
    author_email='pypi@trustworthy.systems',
    install_requires=DEPS,
)
