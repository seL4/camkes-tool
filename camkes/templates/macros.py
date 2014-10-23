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

def marshal(buffer, param, size, pointer=False):
    return '%(buffer)s = camkes_marshal(%(buffer)s, %(amp)s%(param)s, ' \
        '%(size)s);' % {
            'buffer':buffer,
            'amp':'&' if not pointer else '',
            'param':param,
            'size':size,
        }

def unmarshal(buffer, param, size, pointer=False):
    return '%(buffer)s = camkes_unmarshal(%(buffer)s, %(amp)s%(param)s, ' \
        '%(size)s);' % {
            'buffer':buffer,
            'amp':'&' if not pointer else '',
            'param':param,
            'size':size,
        }

def marshal_string(buffer, param, pointer=False):
    return '%(buffer)s = camkes_marshal_string(%(buffer)s, ' \
        '%(star)s%(param)s);' % {
            'buffer':buffer,
            'star':'*' if pointer else '',
            'param':param,
        }

def unmarshal_string(buffer, param, malloc=False, pointer=False):
    s = ''
    if not malloc and pointer:
        s += 'if (strlen((char*)*%(param)s) < strlen(%(buffer)s)) {\n' \
             '    *%(param)s = realloc(*%(param)s, sizeof(char) * ' \
                      '(strlen(%(buffer)s) + 1));\n' \
             '    assert(*%(param)s != NULL);\n' \
             '}\n'
    else:
        if malloc:
            s += '%(star)s%(param)s = malloc(sizeof(char) * ' \
                    '(strlen(%(buffer)s) + 1));\n' \
                 'assert(%(star)s%(param)s != NULL);\n'
    s += '%(buffer)s = camkes_unmarshal_string(%(buffer)s, %(star)s%(param)s);'
    return s % {
        'buffer':buffer,
        'param':param,
        'star':'*' if pointer else '',
    }

def marshal_array(buffer, param, size, pointer=False):
    s = marshal(buffer, '%s_sz' % param, 'sizeof(size_t)', pointer)
    body = marshal(buffer, '(%(star)s%(param)s)[i]' % {
           'star':'*' if pointer else '',
            'param':param,
        }, size)
    s += 'for (int i = 0; i < %(star)s%(param)s_sz; i++) {\n' \
         '    %(body)s\n' \
         '}' % {
             'star':'*' if pointer else '',
             'param':param,
             'body':body,
         }

def unmarshal_array(buffer, param, size, pointer=False, malloc_cast=''):
    star = '*' if pointer else ''
    s = 'size_t %s_sz_ret;\n' % param
    s += unmarshal(buffer, '%s_sz_ret' % param, 'sizeof(size_t)')
    s += 'if (%(star)s%(param)s_sz < %(param)s_sz_ret) {\n' \
         '    %(star)s%(param)s_sz = %(param)s_sz_ret;\n' % {
            'star':star,
            'param':param,
        }
    if malloc_cast:
        s += '%(star)s%(param)s = (%(malloc_cast)s*)realloc(%(star)s%(param)s, ' \
                '%(star)s%(param)s_sz * sizeof(%(malloc_cast)s));\n' \
             'assert(%(param)s != NULL);\n' % {
                    'star':star,
                    'param':param,
                    'malloc_cast':malloc_cast,
                }
    s += '}\n'

    body = unmarshal(buffer, '(%(star)s%(param)s)[i]' % {
            'star':star,
            'param':param,
        }, size)
    s += 'for (int i = 0; i < %(star)s%(param)s_sz; i++) {\n' \
         '    %(body)s\n' \
         '}' % {
             'star':star,
             'param':param,
             'body':body,
         }

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
