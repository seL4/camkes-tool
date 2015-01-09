#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''Brief wrapper around the jinja2 templating engine.'''

import Context
from camkes.internal.version import version
from camkes.templates import TEMPLATES

import jinja2, os

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

class Renderer(object):
    def __init__(self, template_paths, options):

        # PERF: This function is simply constructing a Jinja environment and
        # would be trivial, except that we optimise re-execution of template
        # code by compiling the templates to Python bytecode the first time
        # they are seen. This happens when the compilation cache is enabled and
        # should speed the execution of the template code itself in future
        # runs.

        # Directory in which to store and fetch pre-compiled Jinja2 templates.
        template_cache = os.path.join(options.cache_dir, version(),
            'precompiled-templates')

        loaders = []
        if options.cache in ['on', 'readonly'] and \
                os.path.exists(template_cache):
            # Pre-compiled templates.
            loaders.append(jinja2.ModuleLoader(template_cache))

        # Source templates.
        loaders.extend(map(jinja2.FileSystemLoader, template_paths))

        self.env = jinja2.Environment(
            loader=jinja2.ChoiceLoader(loaders),
            extensions=["jinja2.ext.do", "jinja2.ext.loopcontrols"],
            block_start_string=START_BLOCK,
            block_end_string=END_BLOCK,
            variable_start_string=START_VARIABLE,
            variable_end_string=END_VARIABLE,
            comment_start_string=START_COMMENT,
            comment_end_string=END_COMMENT)

        if options.cache in ['on', 'writeonly'] and \
                not os.path.exists(template_cache):
            # The pre-compiled template cache is enabled but does not exist.
            # We build it here for next time.

            # We filter the templates that Jinja compiles to only the ones we
            # know of in order to avoid errors or wasted time on other stray
            # garbage in the template directory (vim swp files, pycs, ...).
            templates = list(get_leaves(TEMPLATES))

            os.makedirs(template_cache)
            self.env.compile_templates(template_cache,
                filter_func=(lambda x: x in templates), zip=None,
                ignore_errors=False, py_compile=True)

    def render(self, me, configuration, template, obj_space, cap_space, shmem,
            **kwargs):
        context = Context.new_context(me, configuration, obj_space, cap_space,
            shmem, **kwargs)

        t = self.env.get_template(template)
        return t.render(context)
