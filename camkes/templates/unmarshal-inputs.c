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
/*? assert(isinstance(methods_len, six.integer_types)) ?*/          /*# Total number of methods in this interface #*/
/*? assert(isinstance(input_parameters, (list, tuple))) ?*/    /*# All input parameters to this method #*/

/*- for p in input_parameters -*/
  /*- set size = c_symbol('size') -*/
  /*- set offset = c_symbol('offset') -*/
  static unsigned /*? function ?*/_/*? p.name ?*/(unsigned /*? size ?*/, unsigned /*? offset ?*/,
    /*- if p.array -*/
      size_t * /*? p.name ?*/_sz,
      /*- if p.type == 'string' -*/
        char *** /*? p.name ?*/
      /*- else -*/
        /*? macros.show_type(p.type) ?*/ ** /*? p.name ?*/
      /*- endif -*/
    /*- elif p.type == 'string' -*/
      char ** /*? p.name ?*/
    /*- else -*/
      /*? macros.show_type(p.type) ?*/ * /*? p.name ?*/
    /*- endif -*/
  ) {

    /*- set base = c_symbol('buffer_base') -*/
    void * /*? base ?*/ UNUSED = (void*)(/*? buffer ?*/);

    /*- if p.array -*/
      ERR_IF(/*? offset ?*/ + sizeof(* /*? p.name ?*/_sz) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_MALFORMED_RPC_PAYLOAD,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "truncated message encountered while unmarshalling /*? p.name ?*/ in /*? name ?*/",
          .length = /*? size ?*/,
          .current_index = /*? offset ?*/ + sizeof(* /*? p.name ?*/_sz),
        }), ({
          return UINT_MAX;
        }));
      memcpy(/*? p.name ?*/_sz, /*? base ?*/ + /*? offset ?*/, sizeof(* /*? p.name ?*/_sz));
      /*? offset ?*/ += sizeof(* /*? p.name ?*/_sz);
      /*- if p.type == 'string' -*/
        * /*? p.name ?*/ = malloc(sizeof(char*) * (* /*? p.name ?*/_sz));
        ERR_IF(* /*? p.name ?*/ == NULL, /*? error_handler ?*/, ((camkes_error_t){
            .type = CE_ALLOCATION_FAILURE,
            .instance = "/*? instance ?*/",
            .interface = "/*? interface ?*/",
            .description = "out of memory while unmarshalling /*? p.name ?*/ in /*? name ?*/",
            .alloc_bytes = sizeof(char*) * (* /*? p.name ?*/_sz),
          }), ({
            return UINT_MAX;
          }));
      /*- else -*/
        * /*? p.name ?*/ = malloc(sizeof((* /*? p.name ?*/)[0]) * (* /*? p.name ?*/_sz));
        ERR_IF(* /*? p.name ?*/ == NULL, /*? error_handler ?*/, ((camkes_error_t){
            .type = CE_ALLOCATION_FAILURE,
            .instance = "/*? instance ?*/",
            .interface = "/*? interface ?*/",
            .description = "out of memory while unmarshalling /*? p.name ?*/ in /*? name ?*/",
            .alloc_bytes = sizeof((* /*? p.name ?*/)[0]) * (* /*? p.name ?*/_sz),
          }), ({
            return UINT_MAX;
          }));
      /*- endif -*/
      /*- if p.type == 'string' -*/
        /*- set lcount = c_symbol() -*/
        for (int /*? lcount ?*/ = 0; /*? lcount ?*/ < * /*? p.name ?*/_sz; /*? lcount ?*/ ++) {
          /*- set strlen = c_symbol('strlen') -*/
          size_t /*? strlen ?*/ = strnlen(/*? base ?*/ + /*? offset ?*/, /*? size ?*/ - /*? offset ?*/);
          ERR_IF(/*? strlen ?*/ >= /*? size ?*/ - /*? offset ?*/, /*? error_handler ?*/, ((camkes_error_t){
              .type = CE_MALFORMED_RPC_PAYLOAD,
              .instance = "/*? instance ?*/",
              .interface = "/*? interface ?*/",
              .description = "truncated message encountered while unmarshalling /*? p.name ?*/ in /*? name ?*/",
              .length = /*? size ?*/,
              .current_index = /*? offset ?*/ + /*? strlen ?*/ + 1,
            }), ({
              /*- set mcount = c_symbol() -*/
              for (int /*? mcount ?*/ = 0; /*? mcount ?*/ < /*? lcount ?*/; /*? mcount ?*/ ++) {
                free((* /*? p.name ?*/)[/*? mcount ?*/]);
              }
              free(* /*? p.name ?*/);
              return UINT_MAX;
            }));
          /* If we didn't trigger an error, we now know this strdup is safe. */
          (* /*? p.name ?*/)[/*? lcount ?*/] = strdup(/*? base ?*/ + /*? offset ?*/);
          ERR_IF((* /*? p.name ?*/)[/*? lcount ?*/] == NULL, /*? error_handler ?*/, ((camkes_error_t){
              .type = CE_ALLOCATION_FAILURE,
              .instance = "/*? instance ?*/",
              .interface = "/*? interface ?*/",
              .description = "out of memory while unmarshalling /*? p.name ?*/ in /*? name ?*/",
              .alloc_bytes = /*? strlen ?*/ + 1,
            }), ({
              /*- set mcount = c_symbol() -*/
              for (int /*? mcount ?*/ = 0; /*? mcount ?*/ < /*? lcount ?*/; /*? mcount ?*/ ++) {
                free((* /*? p.name ?*/)[/*? mcount ?*/]);
              }
              free(* /*? p.name ?*/);
              return UINT_MAX;
            }));
          /*? offset ?*/ += /*? strlen ?*/ + 1;
        }
      /*- else -*/
        ERR_IF(/*? offset ?*/ + sizeof((* /*? p.name ?*/)[0]) * (* /*? p.name ?*/_sz) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
            .type = CE_MALFORMED_RPC_PAYLOAD,
            .instance = "/*? instance ?*/",
            .interface = "/*? interface ?*/",
            .description = "truncated message encountered while unmarshalling /*? p.name ?*/ in /*? name ?*/",
            .length = /*? size ?*/,
            .current_index = /*? offset ?*/ + sizeof((* /*? p.name ?*/)[0]) * (* /*? p.name ?*/_sz),
          }), ({
            free(* /*? p.name ?*/);
            return UINT_MAX;
          }));
        memcpy(* /*? p.name ?*/, /*? base ?*/ + /*? offset ?*/, sizeof((* /*? p.name ?*/)[0]) * (* /*? p.name ?*/_sz));
        /*? offset ?*/ += sizeof((* /*? p.name ?*/)[0]) * (* /*? p.name ?*/_sz);
      /*- endif -*/
    /*- elif p.type == 'string' -*/
      /*- set strlen = c_symbol('strlen') -*/
      size_t /*? strlen ?*/ = strnlen(/*? base ?*/ + /*? offset ?*/, /*? size ?*/ - /*? offset ?*/);
      ERR_IF(/*? strlen ?*/ >= /*? size ?*/ - /*? offset ?*/, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_MALFORMED_RPC_PAYLOAD,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "truncated message encountered while unmarshalling /*? p.name ?*/ in /*? name ?*/",
          .length = /*? size ?*/,
          .current_index = /*? offset ?*/ + /*? strlen ?*/ + 1,
        }), ({
          return UINT_MAX;
        }));
      * /*? p.name ?*/ = strdup(/*? base ?*/ + /*? offset ?*/);
      ERR_IF(* /*? p.name ?*/ == NULL, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_ALLOCATION_FAILURE,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "out of memory while unmarshalling /*? p.name ?*/ in /*? name ?*/",
          .alloc_bytes = /*? strlen ?*/ + 1,
        }), ({
          return UINT_MAX;
        }));
      /*? offset ?*/ += /*? strlen ?*/ + 1;
    /*- else -*/
      ERR_IF(/*? offset ?*/ + sizeof(* /*? p.name ?*/) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_MALFORMED_RPC_PAYLOAD,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "truncated message encountered while unmarshalling /*? p.name ?*/ in /*? name ?*/",
          .length = /*? size ?*/,
          .current_index = /*? offset ?*/ + sizeof(* /*? p.name ?*/),
        }), ({
          return UINT_MAX;
        }));
      memcpy(/*? p.name ?*/, /*? base ?*/ + /*? offset ?*/, sizeof(* /*? p.name ?*/));
      /*? offset ?*/ += sizeof(* /*? p.name ?*/);
    /*- endif -*/

    return /*? offset ?*/;
  }
/*- endfor -*/

static int /*? function ?*/(
/*- set size = c_symbol('size') -*/
unsigned /*? size ?*/
/*- if len(input_parameters) > 0 -*/
  ,
/*- endif -*/
/*- for p in input_parameters -*/
  /*- if p.array -*/
    size_t * /*? p.name ?*/_sz,
    /*- if p.type == 'string' -*/
      char *** /*? p.name ?*/
    /*- else -*/
      /*? macros.show_type(p.type) ?*/ ** /*? p.name ?*/
    /*- endif -*/
  /*- elif p.type == 'string' -*/
    char ** /*? p.name ?*/
  /*- else -*/
    /*? macros.show_type(p.type) ?*/ * /*? p.name ?*/
  /*- endif -*/
  /*- if not loop.last -*/
    ,
  /*- endif -*/
/*- endfor -*/
) {

  /*- set length = c_symbol('length') -*/
  unsigned /*? length ?*/ UNUSED = 0;

  /*- set base = c_symbol('buffer_base') -*/
  void * /*? base ?*/ UNUSED = (void*)(/*? buffer ?*/);

  /*- if methods_len > 1 -*/
    /* Step over the method index. */
    /*? length ?*/ += sizeof(
    /*- if methods_len <= 2 ** 8 -*/
      uint8_t
    /*- elif methods_len <= 2 ** 16 -*/
      uint16_t
    /*- elif methods_len <= 2 ** 32 -*/
      uint32_t
    /*- elif methods_len <= 2 ** 64 -*/
      uint64_t
    /*- else -*/
      /*? raise(TemplateError('too many methods in interface %s' % name)) ?*/
    /*- endif -*/
    );
  /*- endif -*/

  /* Unmarshal input parameters. */
  /*- for index, p in enumerate(input_parameters) -*/
    /*? assert(isinstance(p.type, six.string_types)) ?*/
    /*? length ?*/ = /*? function ?*/_/*? p.name ?*/(/*? size ?*/, /*? length ?*/,
      /*- if p.array -*/
        /*? p.name ?*/_sz,
      /*- endif -*/
      /*? p.name ?*/
    );
    if (unlikely(/*? length ?*/ == UINT_MAX)) {
      /*- for q in itertools.islice(input_parameters, index) -*/
        /*- if q.array -*/
          /*- if q.type == 'string' -*/
            /*- set mcount = c_symbol() -*/
            for (int /*? mcount ?*/ = 0; /*? mcount ?*/ < * /*? q.name ?*/_sz; /*? mcount ?*/ ++) {
              free((* /*? q.name ?*/)[/*? mcount ?*/]);
            }
          /*- endif -*/
          free(* /*? q.name ?*/);
        /*- elif q.type == 'string' -*/
          free(* /*? q.name ?*/);
        /*- endif -*/
      /*- endfor -*/
      return -1;
    }
  /*- endfor -*/

  /*- if not allow_trailing_data -*/
    ERR_IF(ROUND_UP_UNSAFE(/*? length ?*/, sizeof(seL4_Word)) != /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
        .type = CE_MALFORMED_RPC_PAYLOAD,
        .instance = "/*? instance ?*/",
        .interface = "/*? interface ?*/",
        .description = "excess trailing bytes after unmarshalling parameters for /*? name ?*/",
        .length = /*? size ?*/,
        .current_index = /*? length ?*/,
      }), ({
        /*- for p in input_parameters -*/
          /*- if p.array -*/
            /*- if p.type == 'string' -*/
              /*- set mcount = c_symbol() -*/
              for (int /*? mcount ?*/ = 0; /*? mcount ?*/ < * /*? p.name ?*/_sz; /*? mcount ?*/ ++) {
                free((* /*? p.name ?*/)[/*? mcount ?*/]);
              }
            /*- endif -*/
            free(* /*? p.name ?*/);
          /*- elif p.type == 'string' -*/
            free(* /*? p.name ?*/);
          /*- endif -*/
        /*- endfor -*/
        return -1;
      }));
  /*- endif -*/

  return 0;
}
