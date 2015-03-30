#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

# Macros for use inside the templates.

def header_guard(filename):
    return '#ifndef %(guard)s\n' \
           '#define %(guard)s\n' % {
               'guard':'_CAMKES_%s_' % filename.upper(),
           }

def header_file(filename):
    return '.'.join(filename.split('.')[:-1]) + '.h'

def thread_stack(sym):
    return 'char %s[ROUND_UP_UNSAFE(CONFIG_CAMKES_DEFAULT_STACK_SIZE, ' \
                'PAGE_SIZE_4K) + PAGE_SIZE_4K * 2]\n' \
           '    __attribute__((externally_visible))\n' \
           '    __attribute__((section("guarded")))\n' \
           '    __attribute__((aligned(PAGE_SIZE_4K)));\n' % sym

def ipc_buffer(sym):
    return 'char %s[PAGE_SIZE_4K * 3]\n' \
           '    __attribute__((externally_visible))\n' \
           '    __attribute__((section("guarded")))\n' \
           '    __attribute__((aligned(PAGE_SIZE_4K)));\n' % sym

def save_ipc_buffer_address(sym):
    return '#ifdef ARCH_IA32\n' \
           '    /* We need to save the address of the IPC buffer (for\n' \
           '     * marshalling/unmarshalling) per-thread. Essentially what we\'re after\n' \
           '     * is TLS. Use the IPC buffer\'s user data word for that. Note that we\n' \
           '     * add a page to skip over the guard page in front of the IPC buffer.\n' \
           '     */\n' \
           '    seL4_SetUserData((seL4_Word)%s + 2 * PAGE_SIZE_4K - sizeof(seL4_IPCBuffer));\n' \
           '#endif\n' % sym

def show_includes(xs, prefix=''):
    s = ''
    for header in xs:
        if header.relative:
            s += '#include "%(prefix)s%(source)s"\n' % {
                'prefix':prefix,
                'source':header.source,
            }
        else:
            s += '#include <%s>\n' % header.source
    return s
