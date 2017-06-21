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
/*? assert(isinstance(method_index, six.integer_types)) ?*/         /*# Index of this method in the containing interface #*/
/*? assert(isinstance(methods_len, six.integer_types)) ?*/          /*# Total number of methods in this interface #*/
/*? assert(isinstance(input_parameters, (list, tuple))) ?*/    /*# All input parameters to this method #*/
/*? assert(isinstance(error_handler, six.string_types)) ?*/ /*# Handler to invoke on error #*/

/*- set name_backup = name -*/
/*- for p in input_parameters -*/
  /*- if p.direction == 'in' -*/
    /*- if p.array -*/
      /*- set array = False -*/
      /*- set type = 'size_t' -*/
      /*- set name = '%s_%s_sz_from' % (name_backup, p.name) -*/
      /*- include 'thread_local.c' -*/
    /*- elif p.type != 'string' -*/
      /*- set array = False -*/
      /*- set type = macros.show_type(p.type) -*/
      /*- set name = '%s_%s_from' % (name_backup, p.name) -*/
      /*- include 'thread_local.c' -*/
    /*- endif -*/
  /*- endif -*/
/*- endfor -*/
/*- set name = name_backup -*/

/*- for p in input_parameters -*/
  /*- set offset = c_symbol('offset') -*/
  static unsigned /*? function ?*/_/*? p.name ?*/(unsigned /*? offset ?*/,
    /*- if p.direction == 'in' -*/
      /*- if p.array -*/
        size_t /*? p.name ?*/_sz,
        /*- if p.type == 'string' -*/
          char ** /*? p.name ?*/
        /*- else -*/
          const /*? macros.show_type(p.type) ?*/ * /*? p.name ?*/
        /*- endif -*/
      /*- elif p.type == 'string' -*/
        const char * /*? p.name ?*/
      /*- else -*/
        /*? macros.show_type(p.type) ?*/ /*? p.name ?*/
      /*- endif -*/
    /*- else -*/
      /*? assert(p.direction in ['refin', 'inout']) ?*/
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
    /*- endif -*/
    ) {

    /*- set base = c_symbol('buffer_base') -*/
    void * /*? base ?*/ UNUSED = (void*)(/*? buffer ?*/);

    /* Construct parameter pointers. We do this here to consolidate where we
     * are taking the address of local variables. In future, we need to avoid
     * doing this for verification.
     */
    /*- set ptr = c_symbol('ptr') -*/
    /*- set ptr_sz = c_symbol('ptr_sz') -*/
    /*- set ptr_str = c_symbol('ptr_str') -*/
    /*- set ptr_arr = c_symbol('ptr_arr') -*/
    /*- if p.direction == 'in' -*/
      /*- if p.array -*/
        size_t * /*? ptr_sz ?*/ = TLS_PTR(/*? name ?*/_/*? p.name ?*/_sz_from, /*? p.name ?*/_sz);
        * /*? ptr_sz ?*/ = /*? p.name ?*/_sz;
        /*- if p.type == 'string' -*/
          char ** /*? ptr_arr ?*/ = /*? p.name ?*/;
        /*- else -*/
          const /*? macros.show_type(p.type) ?*/ * /*? ptr_arr ?*/ = /*? p.name ?*/;
        /*- endif -*/
      /*- elif p.type == 'string' -*/
        const char * /*? ptr_str ?*/ = /*? p.name ?*/;
      /*- else -*/
        /*? macros.show_type(p.type) ?*/ * /*? ptr ?*/ = TLS_PTR(/*? name ?*/_/*? p.name ?*/_from, /*? p.name ?*/);
        * /*? ptr ?*/ = /*? p.name ?*/;
      /*- endif -*/
    /*- else -*/
      /*- if p.array -*/
        const size_t * /*? ptr_sz ?*/ = /*? p.name ?*/_sz;
        /*- if p.type == 'string' -*/
          char ** /*? ptr_arr ?*/ = * /*? p.name ?*/;
        /*- else -*/
          const /*? macros.show_type(p.type) ?*/ * /*? ptr_arr ?*/ = * /*? p.name ?*/;
        /*- endif -*/
      /*- elif p.type == 'string' -*/
        const char * /*? ptr_str ?*/ = * /*? p.name ?*/;
      /*- else -*/
        const /*? macros.show_type(p.type) ?*/ * /*? ptr ?*/ = /*? p.name ?*/;
      /*- endif -*/
    /*- endif -*/

    /*- if p.array -*/
      ERR_IF(/*? offset ?*/ + sizeof(* /*? ptr_sz ?*/) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_BUFFER_LENGTH_EXCEEDED,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "buffer exceeded while marshalling /*? p.name ?*/ in /*? name ?*/",
          .current_length = /*? offset ?*/,
          .target_length = /*? offset ?*/ + sizeof(* /*? ptr_sz ?*/),
        }), ({
          return UINT_MAX;
        }));
      memcpy(/*? base ?*/ + /*? offset ?*/, /*? ptr_sz ?*/, sizeof(* /*? ptr_sz ?*/));
      /*? offset ?*/ += sizeof(* /*? ptr_sz ?*/);
      /*- if p.type == 'string' -*/
        /*- set lcount = c_symbol() -*/
        for (int /*? lcount ?*/ = 0; /*? lcount ?*/ < * /*? ptr_sz ?*/; /*? lcount ?*/ ++) {
          /*- set strlen = c_symbol('strlen') -*/
          size_t /*? strlen ?*/ = strnlen(/*? ptr_arr ?*/[/*? lcount ?*/], /*? size ?*/ - /*? offset ?*/);
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
          (void)strcpy(/*? base ?*/ + /*? offset ?*/, /*? ptr_arr ?*/[/*? lcount ?*/]);
          /*? offset ?*/ += /*? strlen ?*/ + 1;
        }
      /*- else -*/
        ERR_IF(/*? offset ?*/ + sizeof(/*? ptr_arr ?*/[0]) * (* /*? ptr_sz ?*/) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
            .type = CE_BUFFER_LENGTH_EXCEEDED,
            .instance = "/*? instance ?*/",
            .interface = "/*? interface ?*/",
            .description = "buffer exceeded while marshalling /*? p.name ?*/ in /*? name ?*/",
            .current_length = /*? offset ?*/,
            .target_length = /*? offset ?*/ + sizeof(/*? ptr_arr ?*/[0]) * (* /*? ptr_sz ?*/),
          }), ({
            return UINT_MAX;
          }));
        memcpy(/*? base ?*/ + /*? offset ?*/, /*? ptr_arr ?*/, sizeof(/*? ptr_arr ?*/[0]) * (* /*? ptr_sz ?*/));
        /*? offset ?*/ += sizeof(/*? ptr_arr ?*/[0]) * (* /*? ptr_sz ?*/);
      /*- endif -*/
    /*- elif p.type == 'string' -*/
      /*- set strlen = c_symbol('strlen') -*/
      size_t /*? strlen ?*/ = strnlen(/*? ptr_str ?*/, /*? size ?*/ - /*? offset ?*/);
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
      (void)strcpy(/*? base ?*/ + /*? offset ?*/, /*? ptr_str ?*/);
      /*? offset ?*/ += /*? strlen ?*/ + 1;
    /*- else -*/
      ERR_IF(/*? offset ?*/ + sizeof(* /*? ptr ?*/) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_BUFFER_LENGTH_EXCEEDED,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "buffer exceeded while marshalling /*? p.name ?*/ in /*? name ?*/",
          .current_length = /*? offset ?*/,
          .target_length = /*? offset ?*/ + sizeof(* /*? ptr ?*/),
        }), ({
          return UINT_MAX;
        }));
      memcpy(/*? base ?*/ + /*? offset ?*/, /*? ptr ?*/, sizeof(* /*? ptr ?*/));
      /*? offset ?*/ += sizeof(* /*? ptr ?*/);
    /*- endif -*/

    return /*? offset ?*/;
  }
/*- endfor -*/

/*- if methods_len > 1 -*/
  /*- set call = c_symbol('method_index') -*/
  static const
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
  /*? call ?*/ = /*? method_index ?*/;
/*- endif -*/

static unsigned /*? function ?*/(
/*- for p in input_parameters -*/
  /*- if p.direction == 'in' -*/
    /*- if p.array -*/
      size_t /*? p.name ?*/_sz,
      /*- if p.type == 'string' -*/
        char ** /*? p.name ?*/
      /*- else -*/
        const /*? macros.show_type(p.type) ?*/ * /*? p.name ?*/
      /*- endif -*/
    /*- elif p.type == 'string' -*/
      const char * /*? p.name ?*/
    /*- else -*/
      /*? macros.show_type(p.type) ?*/ /*? p.name ?*/
    /*- endif -*/
  /*- else -*/
    /*? assert(p.direction in ['refin', 'inout']) ?*/
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
  /*- endif -*/
  /*- if not loop.last -*/
    ,
  /*- endif -*/
/*- endfor -*/
/*- if len(input_parameters) == 0 -*/
  void
/*- endif -*/
) {

  /*- set length = c_symbol('length') -*/
  unsigned /*? length ?*/ = 0;

  /*- set base = c_symbol('buffer_base') -*/
  void * /*? base ?*/ UNUSED = (void*)(/*? buffer ?*/);

  /*- if methods_len > 1 -*/
    /* Marshal the method index. */
    ERR_IF(/*? length ?*/ + sizeof(/*? call ?*/) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
        .type = CE_BUFFER_LENGTH_EXCEEDED,
        .instance = "/*? instance ?*/",
        .interface = "/*? interface ?*/",
        .description = "buffer exceeded while marshalling method index for /*? name ?*/",
        .current_length = /*? length ?*/,
        .target_length = /*? length ?*/ + sizeof(/*? call ?*/),
      }), ({
        return UINT_MAX;
      }));
    memcpy(/*? base ?*/, & /*? call ?*/, sizeof(/*? call ?*/));
    /*? length ?*/ += sizeof(/*? call ?*/);
  /*- endif -*/

  /* Marshal the parameters. */
  /*- for p in input_parameters -*/
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
    "uncaught buffer overflow while marshalling inputs for /*? name ?*/");

  return /*? length ?*/;
}
