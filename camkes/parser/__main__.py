#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''Entry point for the standalone parser.'''
import os, sys

from camkes.internal.argumentparsing import parse_args
import camkes.internal.constants as constants
import camkes.internal.log as log
from camkes.parser import dedupe, parse_to_ast, resolve_imports, \
    resolve_references, show, pretty, CAmkESSyntaxError

def main():
    # Parse command line arguments.
    options = parse_args(constants.TOOL_PARSER)

    log.set_verbosity(options.verbosity)

    # Parse each source.
    ast = []
    if options.file:
        for f in options.file:
            s = f.read()
            try:
                ast += parse_to_ast(s, options.cpp, options.cpp_flag)
                if options.resolve_imports:
                    ast, _ = resolve_imports(ast, \
                        os.path.dirname(f.name), options.import_path,
                        options.cpp, options.cpp_flag)
            except CAmkESSyntaxError as e:
                e.set_column(s)
                log.error('%s:%s' % (f.name, str(e)))
                return -1
            except Exception:
                log.exception('Error during lexing/parsing \'%s\''% f.name)
                return -1
            finally:
                f.close()
    else:
        s = sys.stdin.read()
        try:
            ast += parse_to_ast(s, options.cpp, options.cpp_flag)
            if options.resolve_imports:
                ast, _ = resolve_imports(ast, \
                    os.curdir, options.import_path, options.cpp,
                    options.cpp_flag)
        except Exception:
            log.exception('Error during lexing/parsing')
            return -1

    ast = dedupe(ast)

    if options.resolve_references:
        ast = resolve_references(ast, options.allow_forward_references)

    # Generate the output and print this.
    out = show(ast)
    print pretty(out)

    return 0

if __name__ == '__main__':
    sys.exit(main())
