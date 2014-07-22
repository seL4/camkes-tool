#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

import camkes.lint as lint
import camkes.parser as parser
import os, sys

from camkes.internal.argumentparsing import parse_args
import camkes.internal.constants as constants
import camkes.internal.log as log

# Return codes:
WARNING, ERROR, CRITICAL = -1, -2, -3

def main():
    args = parse_args(constants.TOOL_LINT)

    log.set_verbosity(args.verbosity)

    # Parse the input and form the AST.
    ast = []
    for f in args.file:
        try:
            items = parser.parse_to_ast(f)
        except Exception as inst:
            log.critical('Failed to parse input: %s' % str(inst))
            return CRITICAL
        if args.resolve_imports:
            try:
                items, _ = parser.resolve_imports(items, \
                    os.path.dirname(f.name), args.import_path)
            except Exception as inst:
                log.critical('Failed to resolve imports: %s' % str(inst))
                return CRITICAL
        ast += items

    if args.resolve_references:
        try:
            ast = parser.resolve_references(ast, args.allow_forward_references)
        except Exception as inst:
            log.critical('Failed to resolve references: %s' % str(inst))
            return CRITICAL

    # Check it for inconsistencies.

    ret = 0

    for m in lint.check(ast):

        if isinstance(m, lint.ProblemWarning):
            log.warning(str(m))
            if ret != ERROR:
                ret = WARNING
        else: # isinstance(m, lint.ProblemError)
            log.error(str(m))
            ret = ERROR

    return ret

if __name__ == '__main__':
    sys.exit(main())
