#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#
#

'''Brief wrapper around the jinja2 templating engine.'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

from .Context import new_context
from camkes.templates import TemplateError

import jinja2
import os
import platform
import six
import sys

# Jinja is setup by default for HTML templating. We tweak the delimiters to
# make it more suitable for C.
START_BLOCK = '/*-'
END_BLOCK = '-*/'
START_VARIABLE = '/*?'
END_VARIABLE = '?*/'
START_COMMENT = '/*#'
END_COMMENT = '#*/'


def get_leaves(d):
    '''Generator that yields the leaves of a hierarchical dictionary. See usage
    below.'''
    assert isinstance(d, dict)
    for v in d.values():
        if isinstance(v, dict):
            # We're at an intermediate node. Yield all leaves below it.
            for x in get_leaves(v):
                yield x
        else:
            # We're at a leaf node.
            yield v


class FileSystemLoaderWithLog(jinja2.FileSystemLoader):

    def __init__(self, path):
        super(FileSystemLoaderWithLog, self).__init__(path)
        self.files = set()

    def get_source(self, environment, template):
        (source, filename, uptodate) = super(
            FileSystemLoaderWithLog, self).get_source(environment, template)
        self.files.add(filename)
        return (source, filename, uptodate)


class Renderer(object):
    def __init__(self, templates):
        # This function constructs a Jinja environment for our templates.

        self.loaders = []

        # Source templates.
        self.loaders.extend(FileSystemLoaderWithLog(os.path.abspath(x)) for x in
                            templates)

        self.env = jinja2.Environment(
            loader=jinja2.ChoiceLoader(self.loaders),
            extensions=["jinja2.ext.do", "jinja2.ext.loopcontrols"],
            block_start_string=START_BLOCK,
            block_end_string=END_BLOCK,
            variable_start_string=START_VARIABLE,
            variable_end_string=END_VARIABLE,
            comment_start_string=START_COMMENT,
            comment_end_string=END_COMMENT,
            auto_reload=False,
            undefined=jinja2.StrictUndefined)

    def render(self, me, assembly, template, render_state, state_key, outfile_name,
               **kwargs):
        context = new_context(me, assembly, render_state, state_key, outfile_name,
                              **kwargs)

        t = self.env.get_template(template)
        try:
            return t.render(context)
        except TemplateError:
            raise
        except Exception as e:
            # Catch and re-cast any other exceptions to allow the runner to
            # handle them as usual and prevent us barfing stack traces when
            # exceptions aren't our fault.
            six.reraise(TemplateError, TemplateError('unhandled exception in '
                                                     'template %s: %s' % (template, e)), sys.exc_info()[2])

    def get_files_used(self):
        files = set()
        for x in self.loaders:
            files |= x.files
        return files
