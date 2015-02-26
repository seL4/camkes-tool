/*# We expect the following variables to be defined when this fragment is
 *# included.
 #*/
/*? assert(isinstance(instance, str)) ?*/      /*# Name of this component instance #*/
/*? assert(isinstance(interface, str)) ?*/     /*# Name of this interface #*/
/*? assert(isinstance(name, str)) ?*/          /*# Name of this method #*/
/*? assert(isinstance(function, str)) ?*/      /*# Name of function to create #*/
/*? assert(isinstance(buffer, str)) ?*/        /*# Buffer symbol (or expression) to marshal into #*/
/*? assert(isinstance(size, str)) ?*/          /*# Length of the buffer; possibly not generation-time constant #*/
/*? assert(isinstance(method_index, int)) ?*/  /*# Index of this method in the containing interface #*/
/*? assert(isinstance(methods_len, int)) ?*/   /*# Total number of methods in this interface #*/
/*? assert(isinstance(input_parameters, list)) ?*/   /*# All input parameters to this method #*/
/*? assert(isinstance(error_handler, str)) ?*/ /*# Handler to invoke on error #*/

/*- for p in input_parameters -*/
  /*- set offset = c_symbol('offset') -*/
  static unsigned int /*? function ?*/_/*? p.name ?*/(unsigned int /*? offset ?*/,
    /*- if p.array -*/
      size_t /*? p.name ?*/_sz,
      /*- if isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
        char ** /*? p.name ?*/
      /*- else -*/
        /*? show(p.type) ?*/ * /*? p.name ?*/
      /*- endif -*/
    /*- elif isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
      char * /*? p.name ?*/
    /*- else -*/
      /*? show(p.type) ?*/ /*? p.name ?*/
    /*- endif -*/
    ) {

    /*- set base = c_symbol('buffer_base') -*/
    void * /*? base ?*/ UNUSED = (void*)(/*? buffer ?*/);

    /*- if p.array -*/
      ERR_IF(/*? offset ?*/ + sizeof(/*? p.name ?*/_sz) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_BUFFER_LENGTH_EXCEEDED,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "buffer exceeded while marshalling /*? p.name ?*/ in /*? name ?*/",
          .current_length = /*? offset ?*/,
          .target_length = /*? offset ?*/ + sizeof(/*? p.name ?*/_sz),
        }), ({
          return UINT_MAX;
        }));
      memcpy(/*? base ?*/ + /*? offset ?*/, & /*? p.name ?*/_sz, sizeof(/*? p.name ?*/_sz));
      /*? offset ?*/ += sizeof(/*? p.name ?*/_sz);
      /*- if isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
        /*- set lcount = c_symbol() -*/
        for (int /*? lcount ?*/ = 0; /*? lcount ?*/ < /*? p.name ?*/_sz; /*? lcount ?*/ ++) {
          /*- set strlen = c_symbol('strlen') -*/
          size_t /*? strlen ?*/ = strnlen(/*? p.name ?*/[/*? lcount ?*/], /*? size ?*/ - /*? offset ?*/);
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
          (void)strcpy(/*? base ?*/ + /*? offset ?*/, /*? p.name ?*/[/*? lcount ?*/]);
          /*? offset ?*/ += /*? strlen ?*/ + 1;
        }
      /*- else -*/
        ERR_IF(/*? offset ?*/ + sizeof(/*? p.name ?*/[0]) * /*? p.name ?*/_sz > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
            .type = CE_BUFFER_LENGTH_EXCEEDED,
            .instance = "/*? instance ?*/",
            .interface = "/*? interface ?*/",
            .description = "buffer exceeded while marshalling /*? p.name ?*/ in /*? name ?*/",
            .current_length = /*? offset ?*/,
            .target_length = /*? offset ?*/ + sizeof(/*? p.name ?*/[0]) * /*? p.name ?*/_sz,
          }), ({
            return UINT_MAX;
          }));
        memcpy(/*? base ?*/ + /*? offset ?*/, /*? p.name ?*/, sizeof(/*? p.name ?*/[0]) * /*? p.name ?*/_sz);
        /*? offset ?*/ += sizeof(/*? p.name ?*/[0]) * /*? p.name ?*/_sz;
      /*- endif -*/
    /*- elif isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
      /*- set strlen = c_symbol('strlen') -*/
      size_t /*? strlen ?*/ = strnlen(/*? p.name ?*/, /*? size ?*/ - /*? offset ?*/);
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
      (void)strcpy(/*? base ?*/ + /*? offset ?*/, /*? p.name ?*/);
      /*? offset ?*/ += /*? strlen ?*/ + 1;
    /*- else -*/
      ERR_IF(/*? offset ?*/ + sizeof(/*? p.name ?*/) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_BUFFER_LENGTH_EXCEEDED,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "buffer exceeded while marshalling /*? p.name ?*/ in /*? name ?*/",
          .current_length = /*? offset ?*/,
          .target_length = /*? offset ?*/ + sizeof(/*? p.name ?*/),
        }), ({
          return UINT_MAX;
        }));
      memcpy(/*? base ?*/ + /*? offset ?*/, & /*? p.name ?*/, sizeof(/*? p.name ?*/));
      /*? offset ?*/ += sizeof(/*? p.name ?*/);
    /*- endif -*/

    return /*? offset ?*/;
  }
/*- endfor -*/

static unsigned int /*? function ?*/(
/*- for p in input_parameters -*/
  /*- if p.array -*/
    size_t /*? p.name ?*/_sz,
    /*- if isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
      char ** /*? p.name ?*/
    /*- else -*/
      /*? show(p.type) ?*/ * /*? p.name ?*/
    /*- endif -*/
  /*- elif isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
    char * /*? p.name ?*/
  /*- else -*/
    /*? show(p.type) ?*/ /*? p.name ?*/
  /*- endif -*/
  /*- if not loop.last -*/
    ,
  /*- endif -*/
/*- endfor -*/
) {

  /*- set length = c_symbol('length') -*/
  unsigned int /*? length ?*/ = 0;

  /*- set base = c_symbol('buffer_base') -*/
  void * /*? base ?*/ UNUSED = (void*)(/*? buffer ?*/);

  /*- if methods_len > 1 -*/
    /* Marshal the method index. */
    /*- set call = c_symbol('method_index') -*/
    /*- if methods_len <= 2 ** 8 -*/
      uint8_t
    /*- elif methods_len <= 2 ** 16 -*/
      uint16_t
    /*- elif methods_len <= 2 ** 32 -*/
      uint32_t
    /*- elif methods_len <= 2 ** 64 -*/
      uint64_t
    /*- else -*/
      /*? raise(Exception('too many methods in interface %s' % name)) ?*/
    /*- endif -*/
    /*? call ?*/ = /*? method_index ?*/;
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
    /*? assert(isinstance(p.type, camkes.ast.Type) or isinstance(p.type, camkes.ast.Reference)) ?*/
    /*? length ?*/ = /*? function ?*/_/*? p.name ?*/(/*? length ?*/,
      /*- if p.array -*/
        /*? p.name ?*/_sz,
      /*- endif -*/
      /*? p.name ?*/
    );
    if (/*? length ?*/ == UINT_MAX) {
      return UINT_MAX;
    }
  /*- endfor -*/

  assert(/*? length ?*/ <= /*? size ?*/ &&
    "uncaught buffer overflow while marshalling inputs for /*? name ?*/");

  return /*? length ?*/;
}
