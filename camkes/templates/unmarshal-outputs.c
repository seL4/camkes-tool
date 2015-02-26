/*# We expect the following variables to be defined when this fragment is
 *# included.
 #*/
/*? assert(isinstance(instance, str)) ?*/      /*# Name of this component instance #*/
/*? assert(isinstance(interface, str)) ?*/     /*# Name of this interface #*/
/*? assert(isinstance(name, str)) ?*/          /*# Name of this method #*/
/*? assert(isinstance(function, str)) ?*/      /*# Name of function to create #*/
/*? assert(isinstance(buffer, str)) ?*/        /*# Buffer symbol (or expression) to marshal into #*/
/*? assert(isinstance(method_index, int)) ?*/  /*# Index of this method in the containing interface #*/
/*? assert(isinstance(output_parameters, list)) ?*/   /*# All output parameters to this method #*/
/*? assert(return_type == None or isinstance(return_type, camkes.ast.Type) or isinstance(return_type, camkes.ast.Reference)) ?*/
                                               /*# Return type of this interface #*/
/*? assert(isinstance(error_handler, str)) ?*/ /*# Handler to invoke on error #*/
/*? assert(isinstance(allow_trailing_data, bool)) ?*/ /*# Whether to ignore checks for remaining bytes after a message #*/

/*- set ret_fn = c_symbol('ret_fn') -*/
/*- if return_type -*/
  /*- set offset = c_symbol('offset') -*/
  /*- set size = c_symbol('size') -*/
  /*- set ret = c_symbol('return') -*/
  static unsigned int /*? function ?*/_/*? ret_fn ?*/(unsigned int /*? size ?*/, unsigned int /*? offset ?*/,
    /*- if return_type.array -*/
      size_t * /*? ret ?*/_sz,
      /*- if isinstance(return_type, camkes.ast.Type) and return_type.type == 'string' -*/
        char ***
      /*- else -*/
        /*? show(return_type) ?*/ **
      /*- endif -*/
    /*- elif isinstance(return_type, camkes.ast.Type) and return_type.type == 'string' -*/
      char **
    /*- else -*/
      /*? show(return_type) ?*/ *
    /*- endif -*/
    /*? ret ?*/
  ) {

    /*- set base = c_symbol('buffer_base') -*/
    void * /*? base ?*/ UNUSED = (void*)(/*? buffer ?*/);

    /* Unmarshal the return value. */
    /*- if return_type.array -*/
      ERR_IF(/*? offset ?*/ + sizeof(* /*? ret ?*/_sz) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_MALFORMED_RPC_PAYLOAD,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "truncated message encountered while unmarshalling return value for /*? name ?*/",
          .length = /*? size ?*/,
          .current_index = /*? offset ?*/ + sizeof(* /*? ret ?*/_sz),
        }), ({
          return UINT_MAX;
        }));
      memcpy(/*? ret ?*/_sz, /*? base ?*/ + /*? offset ?*/, sizeof(* /*? ret ?*/_sz));
      /*? offset ?*/ += sizeof(* /*? ret ?*/_sz);
      /*- if isinstance(return_type, camkes.ast.Type) and return_type.type == 'string' -*/
        * /*? ret ?*/ = malloc(sizeof(char*) * (* /*? ret ?*/_sz));
        ERR_IF(* /*? ret ?*/ == NULL, /*? error_handler ?*/, ((camkes_error_t){
            .type = CE_ALLOCATION_FAILURE,
            .instance = "/*? instance ?*/",
            .interface = "/*? interface ?*/",
            .description = "out of memory while unmarshalling return value for /*? name ?*/",
            .alloc_bytes = sizeof(char*) * (* /*? ret ?*/_sz),
          }), ({
            return UINT_MAX;
          }));
      /*- else -*/
        * /*? ret ?*/ = malloc(sizeof((* /*? ret ?*/)[0]) * (* /*? ret ?*/_sz));
        ERR_IF(* /*? ret ?*/ == NULL, /*? error_handler ?*/, ((camkes_error_t){
            .type = CE_ALLOCATION_FAILURE,
            .instance = "/*? instance ?*/",
            .interface = "/*? interface ?*/",
            .description = "out of memory while unmarshalling return value for /*? name ?*/",
            .alloc_bytes = sizeof((* /*? ret ?*/)[0]) * (* /*? ret ?*/_sz),
          }), ({
            return UINT_MAX;
          }));
      /*- endif -*/
      /*- if isinstance(return_type, camkes.ast.Type) and return_type.type == 'string' -*/
        /*- set lcount = c_symbol() -*/
        for (int /*? lcount ?*/ = 0; /*? lcount ?*/ < * /*? ret ?*/_sz; /*? lcount ?*/ ++) {
          /*- set strlen = c_symbol('strlen') -*/
          size_t /*? strlen ?*/ = strnlen(/*? base ?*/ + /*? offset ?*/, /*? size ?*/ - /*? offset ?*/);
          ERR_IF(/*? strlen ?*/ >= /*? size ?*/ - /*? offset ?*/, /*? error_handler ?*/, ((camkes_error_t){
              .type = CE_MALFORMED_RPC_PAYLOAD,
              .instance = "/*? instance ?*/",
              .interface = "/*? interface ?*/",
              .description = "truncated message encountered while unmarshalling return value for /*? name ?*/",
              .length = /*? size ?*/,
              .current_index = /*? offset ?*/ + /*? strlen ?*/ + 1,
            }), ({
              /*- set mcount = c_symbol() -*/
              for (int /*? mcount ?*/ = 0; /*? mcount ?*/ < /*? lcount ?*/; /*? mcount ?*/ ++) {
                free((* /*? ret ?*/)[/*? mcount ?*/]);
              }
              free(* /*? ret ?*/);
              return UINT_MAX;
            }));
          /* If we didn't trigger an error, we now know this strdup is safe. */
          (* /*? ret ?*/)[/*? lcount ?*/] = strdup(/*? base ?*/ + /*? offset ?*/);
          ERR_IF((* /*? ret ?*/)[/*? lcount ?*/] == NULL, /*? error_handler ?*/, ((camkes_error_t){
              .type = CE_ALLOCATION_FAILURE,
              .instance = "/*? instance ?*/",
              .interface = "/*? interface ?*/",
              .description = "out of memory while unmarshalling return value for /*? name ?*/",
              .alloc_bytes = /*? strlen ?*/ + 1,
            }), ({
              /*- set mcount = c_symbol() -*/
              for (int /*? mcount ?*/ = 0; /*? mcount ?*/ < /*? lcount ?*/; /*? mcount ?*/ ++) {
                free((* /*? ret ?*/)[/*? mcount ?*/]);
              }
              free(* /*? ret ?*/);
              return UINT_MAX;
            }));

          /*? offset ?*/ += /*? strlen ?*/ + 1;
        }
      /*- else -*/
        ERR_IF(/*? offset ?*/ + sizeof((* /*? ret ?*/)[0]) * (* /*? ret ?*/_sz) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
            .type = CE_MALFORMED_RPC_PAYLOAD,
            .instance = "/*? instance ?*/",
            .interface = "/*? interface ?*/",
            .description = "truncated message encountered while unmarshalling return value for /*? name ?*/",
            .length = /*? size ?*/,
            .current_index = /*? offset ?*/ + sizeof((* /*? ret ?*/)[0]) * (* /*? ret ?*/_sz),
          }), ({
            free(* /*? ret ?*/);
            return UINT_MAX;
          }));
        memcpy((* /*? ret ?*/), /*? base ?*/ + /*? offset ?*/, sizeof((* /*? ret ?*/)[0]) * (* /*? ret ?*/_sz));
        /*? offset ?*/ += sizeof((* /*? ret ?*/[0])) * (* /*? ret ?*/_sz);
      /*- endif -*/
    /*- elif isinstance(return_type, camkes.ast.Type) and return_type.type == 'string' -*/
      /*- set strlen = c_symbol('strlen') -*/
      size_t /*? strlen ?*/ = strnlen(/*? base ?*/ + /*? offset ?*/, /*? size ?*/ - /*? offset ?*/);
      ERR_IF(/*? strlen ?*/ >= /*? size ?*/ - /*? offset ?*/, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_MALFORMED_RPC_PAYLOAD,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "truncated message encountered while unmarshalling return value for /*? name ?*/",
          .length = /*? size ?*/,
          .current_index = /*? offset ?*/ + /*? strlen ?*/ + 1,
        }), ({
          return UINT_MAX;
        }));
      * /*? ret ?*/ = strdup(/*? base ?*/ + /*? offset ?*/);
      ERR_IF(* /*? ret ?*/ == NULL, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_ALLOCATION_FAILURE,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "out of memory while unmarshalling return value for /*? name ?*/",
          .alloc_bytes = /*? strlen ?*/ + 1,
        }), ({
          return UINT_MAX;
        }));
      /*? offset ?*/ += /*? strlen ?*/ + 1;
    /*- else -*/
      ERR_IF(/*? offset ?*/ + sizeof(* /*? ret ?*/) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_MALFORMED_RPC_PAYLOAD,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "truncated message encountered while unmarshalling return value for /*? name ?*/",
          .length = /*? size ?*/,
          .current_index = /*? offset ?*/ + sizeof(* /*? ret ?*/),
        }), ({
          return UINT_MAX;
        }));
      memcpy(/*? ret ?*/, /*? base ?*/ + /*? offset ?*/, sizeof(* /*? ret ?*/));
      /*? offset ?*/ += sizeof(* /*? ret ?*/);
    /*- endif -*/

    return /*? offset ?*/;
  }
/*- endif -*/
/*- for p in output_parameters -*/
  /*- set size = c_symbol('size') -*/
  /*- set offset = c_symbol('offset') -*/
  static unsigned int /*? function ?*/_/*? p.name ?*/(unsigned int /*? size ?*/, unsigned int /*? offset ?*/,
    /*- if p.array -*/
      size_t * /*? p.name ?*/_sz,
      /*- if isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
        char *** /*? p.name ?*/
      /*- else -*/
        /*? show(p.type) ?*/ ** /*? p.name ?*/
      /*- endif -*/
    /*- elif isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
      char ** /*? p.name ?*/
    /*- else -*/
      /*? show(p.type) ?*/ * /*? p.name ?*/
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
      /*- if p.direction.direction == 'inout' -*/
        /*- if isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
          /*- set mcount = c_symbol() -*/
          for (int /*? mcount ?*/ = 0; /*? mcount ?*/ < * /*? p.name ?*/_sz; /*? mcount ?*/ ++) {
            free((* /*? p.name ?*/)[/*? mcount ?*/]);
          }
        /*- endif -*/
        free(* /*? p.name ?*/);
      /*- endif -*/
      /*- if isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
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
      /*- if isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
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
        memcpy((* /*? p.name ?*/), /*? base ?*/ + /*? offset ?*/, sizeof((* /*? p.name ?*/)[0]) * (* /*? p.name ?*/_sz));
        /*? offset ?*/ += sizeof((* /*? p.name ?*/)[0]) * (* /*? p.name ?*/_sz);
      /*- endif -*/
    /*- elif isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
      /*- if p.direction.direction == 'inout' -*/
        free(* /*? p.name ?*/);
      /*- endif -*/
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

static int
/*? function ?*/(
/*- set size = c_symbol('size') -*/
unsigned int /*? size ?*/
/*- if return_type or len(output_parameters) > 0 -*/
  ,
/*- endif -*/
/*- set ret = c_symbol('return') -*/
/*- if return_type -*/
  /*- if return_type.array -*/
    size_t * /*? ret ?*/_sz,
    /*- if isinstance(return_type, camkes.ast.Type) and return_type.type == 'string' -*/
      char ***
    /*- else -*/
      /*? show(return_type) ?*/ **
    /*- endif -*/
  /*- elif isinstance(return_type, camkes.ast.Type) and return_type.type == 'string' -*/
    char **
  /*- else -*/
    /*? show(return_type) ?*/ *
  /*- endif -*/
  /*? ret ?*/
  /*- if len(output_parameters) > 0 -*/
    ,
  /*- endif -*/
/*- endif -*/
/*- for p in output_parameters -*/
  /*- if p.array -*/
    size_t * /*? p.name ?*/_sz,
    /*- if isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
      char *** /*? p.name ?*/
    /*- else -*/
      /*? show(p.type) ?*/ ** /*? p.name ?*/
    /*- endif -*/
  /*- elif isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
    char ** /*? p.name ?*/
  /*- else -*/
    /*? show(p.type) ?*/ * /*? p.name ?*/
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

  /*- if return_type -*/
    /*? length ?*/ = /*? function ?*/_/*? ret_fn ?*/(/*? size ?*/, /*? length ?*/,
      /*- if return_type.array -*/
        /*? ret ?*/_sz,
      /*- endif -*/
      /*? ret ?*/
    );
    if (/*? length ?*/ == UINT_MAX) {
      return -1;
    }
  /*- endif -*/

  /* Unmarshal the parameters. */
  /*- for p in output_parameters -*/
    /*? assert(isinstance(p.type, camkes.ast.Type) or isinstance(p.type, camkes.ast.Reference)) ?*/
    /*? length ?*/ = /*? function ?*/_/*? p.name ?*/(/*? size ?*/, /*? length ?*/,
      /*- if p.array -*/
        /*? p.name ?*/_sz,
      /*- endif -*/
      /*? p.name ?*/
    );
    if (/*? length ?*/ == UINT_MAX) {
      /*- if return_type -*/
        /*- if return_type.array -*/
          /*- if isinstance(return_type, camkes.ast.Type) and return_type.type == 'string' -*/
            /*- set mcount = c_symbol() -*/
            for (int /*? mcount ?*/ = 0; /*? mcount ?*/ < * /*? ret ?*/_sz; /*? mcount ?*/ ++) {
              free((* /*? ret ?*/)[/*? mcount ?*/]);
            }
          /*- endif -*/
          free(* /*? ret ?*/);
        /*- elif isinstance(return_type, camkes.ast.Type) and return_type.type == 'string' -*/
          free(* /*? ret ?*/);
        /*- endif -*/
      /*- endif -*/
      /*- for q in output_parameters -*/
        /*- if q == p -*/
          /*- do break -*/
        /*- endif -*/
        /*- if q.array -*/
          /*- if isinstance(q.type, camkes.ast.Type) and q.type.type == 'string' -*/
            /*- set mcount = c_symbol() -*/
            for (int /*? mcount ?*/ = 0; /*? mcount ?*/ < * /*? q.name ?*/_sz; /*? mcount ?*/ ++) {
              free((* /*? q.name ?*/)[/*? mcount ?*/]);
            }
          /*- endif -*/
          free(* /*? q.name ?*/);
        /*- elif isinstance(q.type, camkes.ast.Type) and q.type.type == 'string' -*/
          free(* /*? q.name ?*/);
        /*- endif -*/
      /*- endfor -*/
      return -1;
    }
  /*- endfor -*/

  /*- if not allow_trailing_data -*/
    ERR_IF(ROUND_UP(/*? length ?*/, sizeof(seL4_Word)) != /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
        .type = CE_MALFORMED_RPC_PAYLOAD,
        .instance = "/*? instance ?*/",
        .interface = "/*? interface ?*/",
        .description = "excess trailing bytes after unmarshalling parameters for /*? name ?*/",
        .length = /*? size ?*/,
        .current_index = /*? length ?*/,
      }), ({
        /*- if return_type -*/
          /*- if return_type.array -*/
            /*- if isinstance(return_type, camkes.ast.Type) and return_type.type == 'string' -*/
              /*- set mcount = c_symbol() -*/
              for (int /*? mcount ?*/ = 0; /*? mcount ?*/ < * /*? ret ?*/_sz; /*? mcount ?*/ ++) {
                free((* /*? ret ?*/)[/*? mcount ?*/]);
              }
            /*- endif -*/
            free(* /*? ret ?*/);
          /*- elif isinstance(return_type, camkes.ast.Type) and return_type.type == 'string' -*/
            free(* /*? ret ?*/);
          /*- endif -*/
        /*- endif -*/
        /*- for p in output_parameters -*/
          /*- if p.array -*/
            /*- if isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
              /*- set mcount = c_symbol() -*/
              for (int /*? mcount ?*/ = 0; /*? mcount ?*/ < * /*? p.name ?*/_sz; /*? mcount ?*/ ++) {
                free((* /*? p.name ?*/)[/*? mcount ?*/]);
              }
            /*- endif -*/
            free(* /*? p.name ?*/);
          /*- elif isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
            free(* /*? p.name ?*/);
          /*- endif -*/
        /*- endfor -*/
        return -1;
      }));
  /*- endif -*/

  return 0;
}
