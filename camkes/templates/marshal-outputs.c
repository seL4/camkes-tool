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

/*# We expect the following variables to be defined when this fragment is
 *# included.
 #*/
/*? assert(isinstance(instance, six.string_types)) ?*/      /*# Name of this component instance #*/
/*? assert(isinstance(interface, six.string_types)) ?*/     /*# Name of this interface #*/
/*? assert(isinstance(name, six.string_types)) ?*/          /*# Name of this method #*/
/*? assert(isinstance(function, six.string_types)) ?*/      /*# Name of function to create #*/
/*? assert(isinstance(buffer, six.string_types)) ?*/        /*# Buffer symbol (or expression) to marshal into #*/
/*? assert(isinstance(size, six.string_types)) ?*/          /*# Length of the buffer; possibly not generation-time constant #*/
/*? assert(isinstance(output_parameters, (list, tuple))) ?*/   /*# All output parameters to this method #*/
/*? assert(return_type is none or isinstance(return_type, six.string_types)) ?*/
                                               /*# Return type of this interface #*/
/*? assert(isinstance(error_handler, six.string_types)) ?*/ /*# Handler to invoke on error #*/

/*- set ret_fn = c_symbol('ret_fn') -*/
/*- if return_type is not none -*/
  /*- set offset = c_symbol('offset') -*/
  /*- set ret = c_symbol('return') -*/
  static unsigned /*? function ?*/_/*? ret_fn ?*/(unsigned /*? offset ?*/,
    /*- if return_type == 'string' -*/
      char ** /*? ret ?*/
    /*- else -*/
      const /*? macros.show_type(return_type) ?*/ * /*? ret ?*/
    /*- endif -*/
  ) {

    /*- set base = c_symbol('buffer_base') -*/
    void * /*? base ?*/ UNUSED = (void*)(/*? buffer ?*/);

    /* Marshal the return value. */
    /*- if return_type == 'string' -*/
      /*- set strlen = c_symbol('strlen') -*/
      size_t /*? strlen ?*/ = strnlen(* /*? ret ?*/, /*? size ?*/ - /*? offset ?*/);
      ERR_IF(/*? strlen ?*/ >= /*? size ?*/ - /*? offset ?*/, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_BUFFER_LENGTH_EXCEEDED,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "buffer exceeded while marshalling return value for /*? name ?*/",
          .current_length = /*? offset ?*/,
          .target_length = /*? offset ?*/ + /*? strlen ?*/ + 1,
        }), ({
          return UINT_MAX;
        }));
      /* If we didn't trigger an error, we now know this strcpy is safe. */
      (void)strcpy(/*? base ?*/ + /*? offset ?*/, (* /*? ret ?*/));
      /*? offset ?*/ += /*? strlen ?*/ + 1;
    /*- else -*/
      ERR_IF(/*? offset ?*/ + sizeof(* /*? ret ?*/) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_BUFFER_LENGTH_EXCEEDED,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "buffer exceeded while marshalling return value for /*? name ?*/",
          .current_length = /*? offset ?*/,
          .target_length = /*? offset ?*/ + sizeof(* /*? ret ?*/),
        }), ({
          return UINT_MAX;
        }));
      memcpy(/*? base ?*/ + /*? offset ?*/, /*? ret ?*/, sizeof(* /*? ret ?*/));
      /*? offset ?*/ += sizeof(* /*? ret ?*/);
    /*- endif -*/

    return /*? offset ?*/;
  }
/*- endif -*/
/*- for p in output_parameters -*/
  /*- set offset = c_symbol('offset') -*/
  static unsigned /*? function ?*/_/*? p.name ?*/(unsigned /*? offset ?*/,
    /*- if p.array -*/
      const size_t * /*? p.name ?*/_sz,
      /*- if p.type == 'string' -*/
        char *** /*? p.name ?*/
      /*- else -*/
        /*? macros.show_type(p.type) ?*/ ** /*? p.name ?*/
      /*- endif -*/
    /*- elif p.type == 'string' -*/
      char ** /*? p.name ?*/
    /*- else -*/
      const /*? macros.show_type(p.type) ?*/ * /*? p.name ?*/
    /*- endif -*/
  ) {

    /*- set base = c_symbol('buffer_base') -*/
    void * /*? base ?*/ UNUSED = (void*)(/*? buffer ?*/);

    /*- if p.array -*/
      ERR_IF(/*? offset ?*/ + sizeof(* /*? p.name ?*/_sz) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_BUFFER_LENGTH_EXCEEDED,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "buffer exceeded while marshalling /*? p.name ?*/ in /*? name ?*/",
          .current_length = /*? offset ?*/,
          .target_length = /*? offset ?*/ + sizeof(* /*? p.name ?*/_sz),
        }), ({
          return UINT_MAX;
        }));
      memcpy(/*? base ?*/ + /*? offset ?*/, /*? p.name ?*/_sz, sizeof(* /*? p.name ?*/_sz));
      /*? offset ?*/ += sizeof(* /*? p.name ?*/_sz);
      /*- if p.type == 'string' -*/
        /*- set lcount = c_symbol() -*/
        for (int /*? lcount ?*/ = 0; /*? lcount ?*/ < * /*? p.name ?*/_sz; /*? lcount ?*/ ++) {
          /*- set strlen = c_symbol('strlen') -*/
          size_t /*? strlen ?*/ = strnlen((* /*? p.name ?*/)[/*? lcount ?*/], /*? size ?*/ - /*? offset ?*/);
          ERR_IF(/*? strlen ?*/ >= /*? size ?*/ - /*? offset ?*/, /*? error_handler ?*/, ((camkes_error_t){
              .type = CE_BUFFER_LENGTH_EXCEEDED,
              .instance = "/*? instance ?*/",
              .interface = "/*? interface ?*/",
              .description = "buffer exceeded while marshalling /*? p.name ?*/ in /*? name ?*/",
              .current_length = /*? offset ?*/,
              .target_length = /*? offset ?*/ + /*? strlen ?*/ + 1,
            }), ({
              return UINT_MAX;
            }));
          /* If we didn't trigger an error, we now know this strcpy is safe. */
          (void)strcpy(/*? base ?*/ + /*? offset ?*/, (* /*? p.name ?*/)[/*? lcount ?*/]);
          /*? offset ?*/ += /*? strlen ?*/ + 1;
        }
      /*- else -*/
        ERR_IF(/*? offset ?*/ + sizeof((* /*? p.name ?*/)[0]) * (* /*? p.name ?*/_sz) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
            .type = CE_BUFFER_LENGTH_EXCEEDED,
            .instance = "/*? instance ?*/",
            .interface = "/*? interface ?*/",
            .description = "buffer exceeded while marshalling /*? p.name ?*/ in /*? name ?*/",
            .current_length = /*? offset ?*/,
            .target_length = /*? offset ?*/ + sizeof((* /*? p.name ?*/)[0]) * (* /*? p.name ?*/_sz),
          }), ({
            return UINT_MAX;
          }));
        memcpy(/*? base ?*/ + /*? offset ?*/, * /*? p.name ?*/, sizeof((* /*? p.name ?*/)[0]) * (* /*? p.name ?*/_sz));
        /*? offset ?*/ += sizeof((* /*? p.name ?*/)[0]) * (* /*? p.name ?*/_sz);
      /*- endif -*/
    /*- elif p.type == 'string' -*/
      /*- set strlen = c_symbol('strlen') -*/
      size_t /*? strlen ?*/ = strnlen(* /*? p.name ?*/, /*? size ?*/ - /*? offset ?*/);
      ERR_IF(/*? strlen ?*/ >= /*? size ?*/ - /*? offset ?*/, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_BUFFER_LENGTH_EXCEEDED,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "buffer exceeded while marshalling /*? p.name ?*/ in /*? name ?*/",
          .current_length = /*? offset ?*/,
          .target_length = /*? offset ?*/ + /*? strlen ?*/ + 1,
        }), ({
          return UINT_MAX;
        }));
      /* If we didn't trigger an error, we now know this strcpy is safe. */
      (void)strcpy(/*? base ?*/ + /*? offset ?*/, * /*? p.name ?*/);
      /*? offset ?*/ += /*? strlen ?*/ + 1;
    /*- else -*/
      ERR_IF(/*? offset ?*/ + sizeof(* /*? p.name ?*/) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_BUFFER_LENGTH_EXCEEDED,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "buffer exceeded while marshalling /*? p.name ?*/ in /*? name ?*/",
          .current_length = /*? offset ?*/,
          .target_length = /*? offset ?*/ + sizeof(* /*? p.name ?*/),
        }), ({
          return UINT_MAX;
        }));
      memcpy(/*? base ?*/ + /*? offset ?*/, /*? p.name ?*/, sizeof(* /*? p.name ?*/));
      /*? offset ?*/ += sizeof(* /*? p.name ?*/);
    /*- endif -*/

    return /*? offset ?*/;
  }
/*- endfor -*/

static unsigned /*? function ?*/(
/*- set ret = c_symbol('return') -*/
/*- if return_type is not none -*/
  /*- if return_type == 'string' -*/
    char ** /*? ret ?*/
  /*- else -*/
    const /*? macros.show_type(return_type) ?*/ * /*? ret ?*/
  /*- endif -*/
  /*- if len(output_parameters) > 0 -*/
    ,
  /*- endif -*/
/*- endif -*/
/*- for p in output_parameters -*/
  /*- if p.array -*/
    const size_t * /*? p.name ?*/_sz,
    /*- if p.type == 'string' -*/
      char *** /*? p.name ?*/
    /*- else -*/
      /*? macros.show_type(p.type) ?*/ ** /*? p.name ?*/
    /*- endif -*/
  /*- elif p.type == 'string' -*/
    char ** /*? p.name ?*/
  /*- else -*/
    const /*? macros.show_type(p.type) ?*/ * /*? p.name ?*/
  /*- endif -*/
  /*- if not loop.last -*/
    ,
  /*- endif -*/
/*- endfor -*/
/*- if return_type is none and len(output_parameters) == 0 -*/
  void
/*- endif -*/
) {

  /*- set length = c_symbol('length') -*/
  unsigned /*? length ?*/ = 0;

  /*- if return_type is not none -*/
    /*? length ?*/ = /*? function ?*/_/*? ret_fn ?*/(/*? length ?*/,
      /*? ret ?*/
    );
    if (unlikely(/*? length ?*/ == UINT_MAX)) {
      return UINT_MAX;
    }
  /*- endif -*/

  /* Marshal output parameters. */
  /*- for p in output_parameters -*/
    /*? assert(isinstance(p.type, six.string_types)) ?*/
    /*? length ?*/ = /*? function ?*/_/*? p.name ?*/(/*? length ?*/,
      /*- if p.array -*/
        /*? p.name ?*/_sz,
      /*- endif -*/
      /*? p.name ?*/
    );
    if (unlikely(/*? length ?*/ == UINT_MAX)) {
      return UINT_MAX;
    }
  /*- endfor -*/

  assert(/*? length ?*/ <= /*? size ?*/ &&
    "uncaught buffer overflow while marshalling outputs for /*? name ?*/");

  return /*? length ?*/;
}
