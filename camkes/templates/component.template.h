/*#
 *# Copyright 2014, NICTA
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(NICTA_BSD)
 #*/

/*? macros.header_guard(re.sub('\\W', '_', options.outfile.name)) ?*/
#include <camkes/dataport.h>
#include <stdint.h>
#include <stdlib.h>

/*? macros.show_includes(me.type.includes) ?*/
/*- for i in me.type.uses -*/
    /*? macros.show_includes(i.type.includes, '../static/components/' + me.type.name + '/') ?*/
/*- endfor -*/
/*- for i in me.type.provides -*/
    /*? macros.show_includes(i.type.includes, '../static/components/' + me.type.name + '/') ?*/
/*- endfor -*/

const char *get_instance_name(void);

/* Attributes */
/*- for a in me.type.attributes -*/
    extern const /*? show(a.type) ?*/ /*? a.name ?*/;
/*- endfor -*/

/*- for u in me.type.uses + me.type.provides -*/
    /*- for m in u.type.methods -*/
        /*- if m.return_type -*/
            /*- if m.return_type.array -*/
                /*- if isinstance(m.return.type, camkes.ast.Type) and m.return_type.type == 'string' -*/
                    char **
                /*- else -*/
                    /*? show(m.return_type) ?*/ *
                /*- endif -*/
            /*- elif isinstance(m.return_type, camkes.ast.Type) and m.return_type.type == 'string' -*/
                char *
            /*- else -*/
                /*? show(m.return_type) ?*/
            /*- endif -*/
        /*- else -*/
            void
        /*- endif -*/
        /*? u.name ?*/_/*? m.name ?*/(
            /*- if m.return_type and m.return_type.array -*/
                /*- set ret_sz = c_symbol('ret_sz') -*/
                size_t * /*? ret_sz ?*/
                /*- if len(m.parameters) > 0 -*/
                    ,
                /*- endif -*/
            /*- endif -*/
            /*- for p in m.parameters -*/
              /*- if p.direction == 'in' -*/
                /*- if p.array -*/
                  size_t /*? p.name ?*/_sz,
                  /*- if isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
                    char **
                  /*- else -*/
                    const /*? show(p.type) ?*/ *
                  /*- endif -*/
                /*- elif isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
                  const char *
                /*- else -*/
                  /*? show(p.type) ?*/
                /*- endif -*/
                /*? p.name ?*/
              /*- else -*/
                /*? assert(p.direction in ['refin', 'out', 'inout']) ?*/
                /*- if p.array -*/
                  /*- if p.direction == 'refin' -*/
                    const
                  /*- endif -*/
                  size_t * /*? p.name ?*/_sz,
                  /*- if isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
                    char ***
                  /*- else -*/
                    /*? show(p.type) ?*/ **
                  /*- endif -*/
                /*- elif isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
                  char **
                /*- else -*/
                  /*- if p.direction == 'refin' -*/
                    const
                  /*- endif -*/
                  /*? show(p.type) ?*/ *
                /*- endif -*/
                /*? p.name ?*/
              /*- endif -*/
              /*- if not loop.last -*/
                ,
              /*- endif -*/
            /*- endfor -*/
            /*- if (m.return_type is none or not m.return_type.array) and len(m.parameters) == 0 -*/
              void
            /*- endif -*/
        ) /*- if u.optional -*/ __attribute__((weak)) /*- endif -*/;
    /*- endfor -*/
/*- endfor -*/

/*- for c in me.type.consumes -*/
    void /*? c.name ?*/_wait(void)
        /*- if c.optional -*/ __attribute__((weak)) /*- endif -*/;
    int /*? c.name ?*/_poll(void)
        /*- if c.optional -*/ __attribute__((weak)) /*- endif -*/;
    int /*? c.name ?*/_reg_callback(void (*callback)(void*), void *arg)
        /*- if c.optional -*/ __attribute__((weak)) /*- endif -*/;
/*- endfor -*/

/*- for e in me.type.emits -*/
    void /*? e.name ?*/_emit(void);
/*- endfor -*/

/*- for d in me.type.dataports -*/
    extern volatile /*? show(d.type) ?*/ * /*? d.name ?*/
    /*- if d.optional -*/
        __attribute__((weak))
    /*- endif -*/;
/*- endfor -*/

/*- for m in me.type.mutexes -*/
    int /*? m.name ?*/_lock(void);
    int /*? m.name ?*/_unlock(void);
/*- endfor -*/

/*- for s in me.type.semaphores -*/
    int /*? s.name ?*/_wait(void);
    int /*? s.name ?*/_trywait(void);
    int /*? s.name ?*/_post(void);
/*- endfor -*/

/* Entry point expected to be provided by the user. */
int run(void);

/*- set all_interfaces = me.type.provides + me.type.uses + me.type.emits + me.type.consumes + me.type.dataports -*/

/* Optional init functions provided by the user. */
void pre_init(void) __attribute__((weak));
void post_init(void) __attribute__((weak));
/*- for i in all_interfaces -*/
    void /*? i.name ?*/__init(void) __attribute__((weak));

    void /*? i.name ?*/_timing_get_points(char ***points, size_t *size);
    uint64_t /*? i.name ?*/_timing_get_entry(unsigned int iteration, char *point);
    void /*? i.name ?*/_timing_reset(void);
/*- endfor -*/

void set_putchar(void (*putchar)(int c));

#endif
