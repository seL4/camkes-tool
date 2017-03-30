/*#
 *# Copyright 2015, NICTA
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(NICTA_BSD)
 #*/

/*? macros.header_guard(re.sub('\\W', '_', options.outfile.name)) ?*/
#include <camkes/dataport.h>
#include <camkes/error.h>
#include <stdint.h>
#include <stdlib.h>
#include <utils/util.h>

/*? macros.show_includes(me.type.includes) ?*/
/*- for i in me.type.uses -*/
    /*? macros.show_includes(i.type.includes) ?*/
/*- endfor -*/
/*- for i in me.type.provides -*/
    /*? macros.show_includes(i.type.includes) ?*/
/*- endfor -*/

/*# Include connector headers if connectors with headers are used to connect this instance #*/
/*- for connection in me.parent.connections -*/
    /*- for id, end in enumerate(connection.from_ends) -*/
        /*- if end.instance == me and lookup_template("%s/from/header" % connection.type.name, connection) is not none -*/
#include </*? "%s_%s_%d.h" % (end.interface.name, connection.type.name, id) ?*/>
        /*- endif -*/
    /*- endfor -*/
    /*- for id, end in enumerate(connection.to_ends) -*/
        /*- if end.instance == me and lookup_template("%s/to/header" % connection.type.name, connection) is not none -*/
#include </*? "%s_%s_%d.h" % (end.interface.name, connection.type.name, id) ?*/>
        /*- endif -*/
    /*- endfor -*/
/*- endfor -*/

const char *get_instance_name(void);

/* Attributes */
/*- set myconf = configuration[me.name] -*/
/*- for a in me.type.attributes -*/
    /*- set value = myconf.get(a.name) -*/
    extern const /*? macros.show_type(a.type) ?*/ /*? a.name ?*/ /*- if a.array -*/ [/*?len(value)?*/] /*- endif -*/;
/*- endfor -*/

/*- for u in me.type.uses + me.type.provides -*/
    /*- for m in u.type.methods -*/
        /*- if m.return_type is not none -*/
            /*- if m.return_type == 'string' -*/
                char *
            /*- else -*/
                /*? macros.show_type(m.return_type) ?*/
            /*- endif -*/
        /*- else -*/
            void
        /*- endif -*/
        /*? u.name ?*/_/*? m.name ?*/(
            /*- for p in m.parameters -*/
              /*- if p.direction == 'in' -*/
                /*- if p.array -*/
                  size_t /*? p.name ?*/_sz,
                  /*- if p.type == 'string' -*/
                    char **
                  /*- else -*/
                    const /*? macros.show_type(p.type) ?*/ *
                  /*- endif -*/
                /*- elif p.type == 'string' -*/
                  const char *
                /*- else -*/
                  /*? macros.show_type(p.type) ?*/
                /*- endif -*/
                /*? p.name ?*/
              /*- else -*/
                /*? assert(p.direction in ['refin', 'out', 'inout']) ?*/
                /*- if p.array -*/
                  /*- if p.direction == 'refin' -*/
                    const
                  /*- endif -*/
                  size_t * /*? p.name ?*/_sz,
                  /*- if p.type == 'string' -*/
                    char ***
                  /*- else -*/
                    /*? macros.show_type(p.type) ?*/ **
                  /*- endif -*/
                /*- elif p.type == 'string' -*/
                  char **
                /*- else -*/
                  /*- if p.direction == 'refin' -*/
                    const
                  /*- endif -*/
                  /*? macros.show_type(p.type) ?*/ *
                /*- endif -*/
                /*? p.name ?*/
              /*- endif -*/
              /*- if not loop.last -*/
                ,
              /*- endif -*/
            /*- endfor -*/
            /*- if len(m.parameters) == 0 -*/
              void
            /*- endif -*/
        ) NONNULL_ALL /*- if isinstance(u, camkes.ast.Uses) and u.optional -*/ WEAK /*- endif -*/;
    /*- endfor -*/
/*- endfor -*/

/*- for c in me.type.consumes -*/
    /*# HACK: Connection-specific check here to just be nice to the user and
     *# trigger a compile-time warning if they try to use functions that aren't
     *# implemented.
     #*/
    /*- set irq = [False] -*/
    /*- for conn in composition.connections -*/
      /*- if conn.type.name == 'seL4HardwareInterrupt' and id(conn.to_ends[0].interface) == id(c) -*/
        /*- do irq.__setitem__(0, True) -*/
        /*- break -*/
      /*- endif -*/
    /*- endfor -*/
    void /*? c.name ?*/_wait(void)
        /*- if c.optional -*/ WEAK /*- endif -*/
        /*- if irq[0] -*/ WARNING("/*? c.name ?*/_wait is not provided by "
            "seL4HardwareInterrupt") /*- endif -*/
        ;
    int /*? c.name ?*/_poll(void) WARN_UNUSED_RESULT
        /*- if c.optional -*/ WEAK /*- endif -*/
        /*- if irq[0] -*/ WARNING("/*? c.name ?*/_poll is not provided by "
            "seL4HardwareInterrupt") /*- endif -*/
        ;
    int /*? c.name ?*/_reg_callback(void (*callback)(void*), void *arg) WARN_UNUSED_RESULT
        /*- if c.optional -*/ WEAK /*- endif -*/
        /*- if irq[0] -*/ WARNING("/*? c.name ?*/_reg_callback is not provided "
            "by seL4HardwareInterrupt") /*- endif -*/
        ;
    int /*? c.name ?*/_acknowledge(void) WARN_UNUSED_RESULT
        /*- if c.optional -*/ WEAK /*- endif -*/;
    /* Implemented by user code. */
    void /*? c.name ?*/_handle(void);
/*- endfor -*/

/*- for e in me.type.emits -*/
    void /*? e.name ?*/_emit(void);
/*- endfor -*/

/*- for d in me.type.dataports -*/
    extern /*? macros.dataport_type(d.type) ?*/ * /*? d.name ?*/
    /*- if d.optional -*/
        WEAK
    /*- endif -*/;
/*- endfor -*/

/*- for m in me.type.mutexes -*/
    int /*? m.name ?*/_lock(void) WARN_UNUSED_RESULT;
    int /*? m.name ?*/_unlock(void) WARN_UNUSED_RESULT;
/*- endfor -*/

/*- for s in me.type.semaphores -*/
    int /*? s.name ?*/_wait(void) WARN_UNUSED_RESULT;
    int /*? s.name ?*/_trywait(void) WARN_UNUSED_RESULT;
    int /*? s.name ?*/_post(void) WARN_UNUSED_RESULT;
/*- endfor -*/

/*- for b in me.type.binary_semaphores -*/
    int /*? b.name ?*/_wait(void) WARN_UNUSED_RESULT;
    int /*? b.name ?*/_post(void) WARN_UNUSED_RESULT;
/*- endfor -*/

/* Entry point expected to be provided by the user. */
int run(void);

/*- set all_interfaces = me.type.provides + me.type.uses + me.type.emits + me.type.consumes + me.type.dataports -*/

/* Optional init functions provided by the user. */
void pre_init(void) WEAK;
void post_init(void) WEAK;
/*- for i in all_interfaces -*/
    void /*? i.name ?*/__init(void) WEAK;

    void /*? i.name ?*/_timing_get_points(char ***points, size_t *size);
    uint64_t /*? i.name ?*/_timing_get_entry(unsigned iteration, char *point);
    void /*? i.name ?*/_timing_reset(void);
/*- endfor -*/

void set_putchar(void (*putchar)(int c));

/*- for i in all_interfaces -*/
  camkes_error_handler_t /*? i.name ?*/_register_error_handler(
    camkes_error_handler_t handler);
/*- endfor -*/

#endif
