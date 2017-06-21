/*
 * Copyright 2017, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 */

#include <camkes/error.h>
#include <sel4/sel4.h>
#include <sync/sem-bare.h>
#include <utils/util.h>

/*? macros.show_includes(me.instance.type.includes) ?*/

/* Interface-specific error handling. */
/*- set interface = me.interface.name -*/
/*- set error_handler = '%s_error_handler' % me.interface.name -*/
/*- include 'error-handler.c' -*/

/*- set my_index = me.parent.from_ends.index(me) -*/

/*- set eps = [] -*/
/*- for index in six.moves.range(len(me.parent.to_ends)) -*/
  /*- do eps.append(alloc('ep_%d' % index, seL4_EndpointObject, read=True, write=True)) -*/

  char from_/*? my_index ?*/_/*? me.interface.name ?*/_/*? index ?*/_data[ROUND_UP_UNSAFE(sizeof(int), PAGE_SIZE_4K)];
  volatile int *counter_/*? index ?*/ = (volatile int*)from_/*? my_index ?*/_/*? me.interface.name ?*/_/*? index ?*/_data;
  /*? register_shared_variable('%s_%d_data' % (me.parent.name, index), 'from_%d_%s_%d_data' % (my_index, me.interface.name, index), 'RW') ?*/
/*- endfor -*/

void /*? me.interface.name ?*/_emit_underlying(void) {
    int result UNUSED;
    /*- for index, ep in enumerate(eps) -*/
      result = sync_sem_bare_post(/*? ep ?*/, counter_/*? index ?*/);
      ERR_IF(result != 0, /*? error_handler ?*/, ((camkes_error_t){
            .type = CE_OVERFLOW,
            .instance = "/*? me.instance.name ?*/",
            .interface = "/*? me.interface.name ?*/",
            .description = "failed to send event to 'to' end #/*? index ?*/ due to potential overflow",
          }), ({
              return;
          }));
    /*- endfor -*/
}
