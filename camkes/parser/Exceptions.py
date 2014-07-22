#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

def _get_msg(column, token):
    return '%(line)s%(column)sUnexpected token%(token)s' % {
        'line':('%d:' % token.lineno) if token is not None else '',
        'column':('%d:' % column) if column is not None else '',
        'token':(' \'%s\'' % token.value) if token is not None else '',
    }

class CAmkESSyntaxError(SyntaxError):
    def __init__(self, token=None):
        super(CAmkESSyntaxError, self).__init__(_get_msg(None, token))
        self.token = token
        self.column = None

    def set_column(self, context):
        assert context is not None
        assert self.column is None
        if self.token is None:
            return

        # Adapted from 4.6 of the PLY manual.
        last_cr = context.rfind('\n', 0, self.token.lexpos)
        if last_cr < 0:
             last_cr = 0
        self.column = (self.token.lexpos - last_cr) + 1

        self.msg = _get_msg(self.column, self.token)
