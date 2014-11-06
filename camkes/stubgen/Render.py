#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

import jinja2

def render(procedure, template):
    '''Take a simplified CAmkES procedure definition, a template given as a
    string, and instantiate the template with values from the given
    procedure.'''

    # Construct a Jinja environment, overriding the usual tokens with ones that
    # are more friendly to C.
    env = jinja2.Environment(
        extensions=["jinja2.ext.do", "jinja2.ext.loopcontrols"],
        block_start_string='/*-',
        block_end_string='-*/',
        variable_start_string='/*?',
        variable_end_string='?*/',
        comment_start_string='/*#',
        comment_end_string='#*/')
    t = env.from_string(template)

    # Export all the Python builtins and give the template authors a 'me'
    # variable that acts like 'self'.
    return t.render(dict(
        globals()['__builtins__'].items() +
        {'me':procedure}.items()))
