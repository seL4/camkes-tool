/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <camkes/dataport.h>
#include <camkes/error.h>
#include <stdint.h>
#include <stdlib.h>
#include <utils/util.h>
#include <platsupport/io.h>
#include <platsupport/irq.h>

/*? macros.show_includes(me.type.includes) ?*/
/*- for i in me.type.uses -*/
    /*? macros.show_includes(i.type.includes) ?*/
/*- endfor -*/
/*- for i in me.type.provides -*/
    /*? macros.show_includes(i.type.includes) ?*/
/*- endfor -*/

const char *get_instance_name(void);
int get_instance_core(void);

/* Attributes */

// This macro allows using attributes as "rvalues" e.g. in the array size
// declarations. Unfortunately, the C language (in contrast to C++) does not
// support using "lvalues" in this case, even if declared as const.
#define CAMKES_CONST_ATTR(attr) attr##_DEF

/*- set myconf = configuration[me.name] -*/
/*? macros.print_type_definitions(me.type.attributes, myconf) ?*/
/*- for a in me.type.attributes -*/
    /*- set value = myconf.get(a.name) -*/
    /*- if value is not none -*/
        #define /*? a.name ?*/_DEF /*? macros.show_attribute_value(a, value) ?*/
    /*- endif -*/

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
    /*- set dtb_connector = [False] -*/
    /*- for conn in composition.connections -*/
      /*- if conn.type.name == 'seL4HardwareInterrupt' and id(conn.to_ends[0].interface) == id(c) -*/
        /*- do irq.__setitem__(0, True) -*/
        /*- break -*/
      /*- endif -*/
      /*- if conn.type.name == 'seL4DTBHardware' -*/
        /*# We need to loop over ends as there may be multiple 'consumes' devices connected to
         *# the same dummy source, e.g.
         *#     emits Dummy dummy_source;
         *#     consumes Dummy pwm_timer_1;
         *#     consumes Dummy pwm_timer_2;
         *#     ...
         *#     connection seL4DTBHardware pwm_conn_1(from dummy_source, to pwm_timer_1);
         *#     connection seL4DTBHardware pwm_conn_2(from dummy_source, to pwm_timer_2);
         *# the whole connection becomes:
         *#     component.pwm_conn_1.component.pwm_conn_2
         #*/
        /*- for end in conn.to_ends -*/
            /*- if id(end.interface) == id(c) -*/
                /*- do irq.__setitem__(0, True) -*/
                /*- do dtb_connector.__setitem__(0, True) -*/
                /*- break -*/
            /*- endif -*/
        /*- endfor -*/
        /*- if irq[0] -*/
            /*- break -*/
        /*- endif -*/
      /*- endif -*/
    /*- endfor -*/
    void /*? c.name ?*/_wait(void)
        /*- if c.optional -*/ WEAK /*- endif -*/
        /*- if irq[0] -*/ WARNING("/*? c.name ?*/_wait is not provided by "
            "seL4HardwareInterrupt or seL4DTBHardware") /*- endif -*/
        ;
    int /*? c.name ?*/_poll(void) WARN_UNUSED_RESULT
        /*- if c.optional -*/ WEAK /*- endif -*/
        /*- if irq[0] -*/ WARNING("/*? c.name ?*/_poll is not provided by "
            "seL4HardwareInterrupt or seL4DTBHardware") /*- endif -*/
        ;
    int /*? c.name ?*/_reg_callback(void (*callback)(void*), void *arg) WARN_UNUSED_RESULT
        /*- if c.optional -*/ WEAK /*- endif -*/
        /*- if irq[0] -*/ WARNING("/*? c.name ?*/_reg_callback is not provided "
            "by seL4HardwareInterrupt or seL4DTBHardware") /*- endif -*/
        ;
    /*- if dtb_connector[0] -*/
        /*# Since the interfaces of the seL4DTBHardware connector are 'consumes', we
         *# have to declare the buffers here, and not inside the dataport block
         #*/
        /*- set config_name = '%s.%s' % (me.name, c) -*/
        /*- set dtb_config = configuration[config_name]['dtb'] -*/
        /*- if dtb_config is none -*/
            /*? raise(TemplateError('Couldn\'t grab the DTB for the %s seL4DTBHardware connection.' % config_name)) ?*/
        /*- endif -*/
        /*- set dtb_query = dtb_config.get('query') -*/
        /*- if dtb_query is none -*/
            /*? raise(TemplateError('Couldn\'t grab the DTB query for the %s seL4DTBHardware connection.' % config_name)) ?*/
        /*- endif -*/
        /*- if len(dtb_query) != 1 -*/
            /*? raise(TemplateError('Invalid number of DTB paths for the %s seL4DTBHardware connection.' % config_name)) ?*/
        /*- endif -*/
        /*- if dtb_query[0] is none -*/
            /*? raise(TemplateError('Missing DTB path for the %s seL4DTBHardware connection.' % config_name)) ?*/
        /*- endif -*/
        /*- set dtb = dtb_query[0] -*/
        /*- set num_registers = len(dtb['reg']) // (dtb['this_address_cells'][0] + dtb['this_size_cells'][0]) -*/
        /*# Declare all the initialised buffers #*/
        /*- for i in range(0, num_registers) -*/
            extern void * /*? c ?*/_/*? i ?*/;
        /*- endfor -*/
    /*- endif -*/
    /*- if irq[0] and dtb_connector[0] -*/
        int /*? c.name ?*/_irq_acknowledge(ps_irq_t *irq) WARN_UNUSED_RESULT;
        /* Implemented by user code or substituted for the IRQ interface. */
        void /*? c.name ?*/_irq_handle(ps_irq_t *irq) WEAK;
    /*- else -*/
        int /*? c.name ?*/_acknowledge(void) WARN_UNUSED_RESULT
        /*- if c.optional -*/ WEAK /*- endif -*/;
        /* Implemented by user code or substituted for the IRQ interface. */
        void /*? c.name ?*/_handle(void) WEAK;
    /*- endif -*/
/*- endfor -*/

/*- for e in me.type.emits -*/
    void /*? e.name ?*/_emit(void);
/*- endfor -*/

/*- for d in me.type.dataports -*/
    extern /*? macros.dataport_type(d.type) ?*/ * /*? d.name ?*/
    /*- if d.optional -*/
        WEAK
    /*- endif -*/;
    int /*? d.name ?*/_cache_op(size_t start_offset, size_t size, dma_cache_op_t cache_op)
    /*- if d.optional -*/
        __attribute__((weak))
    /*- endif -*/;
    #define /*? d.name ?*/_release() COMPILER_MEMORY_RELEASE()
    #define /*? d.name ?*/_acquire() COMPILER_MEMORY_ACQUIRE()

    #define /*? d.name ?*/_size /*? macros.dataport_size(d.type) ?*/

    static inline size_t /*? d.name ?*/_get_size(void) {
      return /*? macros.dataport_size(d.type) ?*/;
    }
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
