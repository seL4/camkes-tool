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

import jinja2

# Jinja is setup by default for HTML templating. We tweak the delimiters to
# make it more suitable for C.
START_BLOCK = '/*-'
END_BLOCK = '-*/'
START_VARIABLE = '/*?'
END_VARIABLE = '?*/'
START_COMMENT = '/*#'
END_COMMENT = '#*/'

class Renderer(object):
    def __init__(self, template_paths):
        self.env = jinja2.Environment(
            loader=jinja2.ChoiceLoader(map(jinja2.FileSystemLoader, template_paths)),
            extensions=["jinja2.ext.do", "jinja2.ext.loopcontrols"],
            block_start_string=START_BLOCK,
            block_end_string=END_BLOCK,
            variable_start_string=START_VARIABLE,
            variable_end_string=END_VARIABLE,
            comment_start_string=START_COMMENT,
            comment_end_string=END_COMMENT)

    def render(self, me, configuration, template, obj_space, cap_space, shmem,
            **kwargs):
        context = Context.new_context(me, configuration, obj_space, cap_space,
            shmem, **kwargs)

        t = self.env.get_template(template)
        return t.render(context)
