#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''
Argument parsing code for various submodules. This is consolidated here, rather
than in each entry point itself, to allow them to all accept the same (or at
least a subset of the same) arguments without repeating the description of them
everywhere.
'''
import argparse, os, sys
import constants, version

class Tool(object):
    def __init__(self, cmd, desc, args):
        self.cmd = cmd
        self.desc = desc
        self.args = args

# Each tool gets a subset of the available arguments. This map determines which
# they get.
TOOLS = {
    constants.TOOL_LINT : Tool(
        'python -m camkes.lint',
        'Detect inconsistencies and errors in a CAmkES specification.',
        set([
            '--debug',
            '--dont-resolve-references',
            '--dont-resolve-imports',
            '--file',
            '--import-path',
            '--quiet',
            '--resolve-imports',
            '--resolve-references',
            '--verbose',
            '--version',
        ])),
    constants.TOOL_PARSER : Tool(
        'python -m camkes.parser',
        'Parse and output a CAmkES specification.',
        set([
            '--cpp',
            '--cpp-flag',
            '--debug',
            '--dont-resolve-imports',
            '--dont-resolve-references',
            '--file',
            '--import-path',
            '--nocpp',
            '--quiet',
            '--resolve-imports',
            '--resolve-references',
            '--verbose',
            '--version',
        ])),
    constants.TOOL_RUNNER : Tool(
        'python -m camkes.runner',
        'Instantiate templates based on a CAmkES specification.',
        set([
            '--cache',
            '--cache-dir',
            '--cpp',
            '--cpp-flag',
            '--debug',
            '--default-priority',
            '--elf',
            '--file',
            '--frpc-lock-elision',
            '--fno-rpc-lock-elision',
            '--fcall-leave-reply-cap',
            '--fno-call-leave-reply-cap',
            '--fprovide-tcb-caps',
            '--fno-provide-tcb-caps',
            '--fspecialise-syscall-stubs',
            '--fno-specialise-syscall-stubs',
            '--fsupport-init',
            '--fno-support-init',
            '--import-path',
            '--item',
            '--largeframe',
            '--hyp',
            '--nocpp',
            '--outfile',
            '--platform',
            '--ply-optimise',
            '--post-render-edit',
            '--profiler',
            '--profile-log',
            '--prune',
            '--quiet',
            '--templates',
            '--verbose',
            '--version',
        ])),
}

def parse_args(tool):
    assert tool in TOOLS
    t = TOOLS[tool]

    p = argparse.ArgumentParser(prog=t.cmd, description=t.desc)

    def add_arg(opt, *args, **kwargs):
        if opt in t.args:
            p.add_argument(opt, *args, **kwargs)

    add_arg('--file', '-f', \
        help='Add this file to the list of input files to parse. Files are parsed in the order in which they are encountered on the command line.', \
        action='append', \
        type=argparse.FileType('r'))
    add_arg('--cpp', action='store_true',
        help='Pre-process the source with CPP')
    add_arg('--nocpp', action='store_false', dest='cpp',
        help='Do not pre-process the source with CPP')
    add_arg('--cpp-flag', action='append', default=[],
        help='Specify a flag to pass to CPP')
    add_arg('--dont-resolve-imports', '-d', \
        help='When encountering an import statement, record it as such and pass this information through to the final output. That is, don\'t look up and try to parse the imported file.', \
        dest='resolve_imports', \
        action='store_false')
    add_arg('--resolve-imports', '-r', \
        help='When encountering an import statement, look up and parse the imported file.', \
        default=True, \
        dest='resolve_imports', \
        action='store_true')
    add_arg('--dont-resolve-references', \
        help='Don\'t attempt to resolve any references found in the input. Just present these as references in the final AST.', \
        dest='resolve_references', \
        action='store_false')
    add_arg('--resolve-references', '-R', \
        help='After parsing the input (and optionally resolving imports) attempt to resolve references. Any references still present in the final AST could not be resolved to any valid object in the AST.', \
        dest='resolve_references', \
        default=True, \
        action='store_true')
    add_arg('--import-path', '-I', \
        help='Add this path to the list of paths to search for built-in imports. That is, add it to the list of directories that are searched to find the file "foo" when encountering an expression "import <foo>;". Note that this does nothing unless you pass -r/--resolve-imports.', \
        action='append',
        default=[])
    add_arg('--quiet', '-q', \
        help='No output.', \
        dest='verbosity', \
        default=1, \
        action='store_const', \
        const=0)
    add_arg('--verbose', '-v', \
        help='Verbose output.', \
        dest='verbosity', \
        action='store_const', \
        const=2)
    add_arg('--debug', '-D', \
        help='Extra verbose output.', \
        dest='verbosity', \
        action='store_const', \
        const=3)
    add_arg('--outfile', '-O', \
        help='Output to the given file (default stdout).', \
        type=argparse.FileType('w'), \
        required=True)
    add_arg('--elf', '-E', \
        help='ELF files to contribute to a CapDL specification.', \
        action='append')
    add_arg('--item', '-T', \
        help='AST entity to produce code for.', required=True)
    add_arg('--platform', '-p', \
        help='Platform to produce code for. Pass \'help\' to see valid platforms.', \
        default='seL4')
    add_arg('--post-render-edit',
        help='Allow the user to edit rendered templates before exiting.',
        action='store_true')
    add_arg('--profiler',
        help='Set profiling tool for runtime statistics.',
        choices=['none', 'internal', 'native', 'aggregate', 'heartbeat'],
        default='none')
    add_arg('--profile-log',
        help='Log profile statistics to the given file (requires --profiler to be set).',
        type=argparse.FileType('w'),
        default=sys.stdout)
    add_arg('--templates', '-t', \
        help='Extra directory to search for templates (before builtin templates).')
    add_arg('--cache', '-c', default='off',
        choices=['off', 'on', 'readonly', 'writeonly'],
        help='Set code generation cache mode.')
    add_arg('--cache-dir', default=os.path.join(os.path.expanduser('~'), '.camkes/cache'),
        help='Set code generation cache location.')
    add_arg('--version', action='version', version='%(prog)s %(version)s' % {
        'prog':'%(prog)s',
        'version':version.version(),
    })
    add_arg('--frpc-lock-elision', action='store_true', default=True,
        help='Enable lock elision optimisation in seL4RPC connector.')
    add_arg('--fno-rpc-lock-elision', action='store_false',
        dest='frpc_lock_elision',
        help='Disable lock elision optimisation in seL4RPC connector.')
    add_arg('--fcall-leave-reply-cap', action='store_true', default=True,
        help='Enable operating on reply caps in place in seL4Call connector.')
    add_arg('--fno-call-leave-reply-cap', action='store_false',
        dest='fcall_leave_reply_cap',
        help='Disable operating on reply caps in place in seL4Call connector.')
    add_arg('--fspecialise-syscall-stubs', action='store_true', default=True,
        help='Generate inline syscall stubs to reduce overhead where possible.')
    add_arg('--fno-specialise-syscall-stubs', action='store_false',
        dest='fspecialise_syscall_stubs',
        help='Always use the libsel4 syscall stubs.')
    add_arg('--fprovide-tcb-caps', action='store_true', default=True,
        help='Hand out TCB caps to components, allowing them to exit cleanly.')
    add_arg('--fno-provide-tcb-caps', action='store_false',
        dest='fprovide_tcb_caps',
        help='Do not hand out TCB caps, causing components to fault on exiting.')
    add_arg('--fsupport-init', action='store_true', default=True,
        help='Support pre_init, post_init and friends.')
    add_arg('--fno-support-init', action='store_false',
        dest='fsupport_init',
        help='Do not support pre_init, post_init and friends.')
    add_arg('--default-priority', type=int, default=254,
        help='Default component thread priority.')
    add_arg('--prune', action='store_true', \
        help='Minimise the number of functions in generated C files.')
    add_arg('--ply-optimise', action='store_true', \
        help='Run PLY with optimisations enabled.')
    add_arg('--largeframe', action='store_true',
        help='Try to use large frames when possible.')
    add_arg('--hyp', action='store_true',
        help='Assume the target platform\'s kernel is running in HYP mode.')

    return p.parse_args()
