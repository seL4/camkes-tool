/*# We expect the following variables to be defined when this fragment is
 *# included.
 #*/
/*? assert(isinstance(instance, str)) ?*/      /*# Name of this component instance #*/
/*? assert(isinstance(interface, str)) ?*/     /*# Name of this interface #*/
/*? assert(isinstance(name, str)) ?*/          /*# Name of this method #*/
/*? assert(isinstance(function, str)) ?*/      /*# Name of function to create #*/
/*? assert(isinstance(buffer, str)) ?*/        /*# Buffer symbol (or expression) to marshal into #*/
/*? assert(isinstance(methods_len, int)) ?*/   /*# Total number of methods in this interface #*/
/*? assert(isinstance(input_parameters, list)) ?*/   /*# All input parameters to this method #*/

static int /*? function ?*/(
/*- set size = c_symbol('size') -*/
unsigned int /*? size ?*/
/*- if len(input_parameters) > 0 -*/
  ,
/*- endif -*/
/*- for p in input_parameters -*/
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
      /*? raise(Exception('too many methods in interface %s' % name)) ?*/
    /*- endif -*/
    );
  /*- endif -*/
  
  /* Unmarshal input parameters. */
  /*- for p in input_parameters -*/
    /*? assert(isinstance(p.type, camkes.ast.Type) or isinstance(p.type, camkes.ast.Reference)) ?*/
    /*- if p.array -*/
      ERR_IF(/*? length ?*/ + sizeof(* /*? p.name ?*/_sz) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_MALFORMED_RPC_PAYLOAD,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "truncated message encountered while unmarshalling /*? p.name ?*/ in /*? name ?*/",
          .length = /*? size ?*/,
          .current_index = /*? length ?*/ + sizeof(* /*? p.name ?*/_sz),
        }), ({
          /*- for q in input_parameters -*/
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
        }));
      memcpy(/*? p.name ?*/_sz, /*? base ?*/ + /*? length ?*/, sizeof(* /*? p.name ?*/_sz));
      /*? length ?*/ += sizeof(* /*? p.name ?*/_sz);
      /*- if isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
        * /*? p.name ?*/ = malloc(sizeof(char*) * (* /*? p.name ?*/_sz));
        ERR_IF(* /*? p.name ?*/ == NULL, /*? error_handler ?*/, ((camkes_error_t){
            .type = CE_ALLOCATION_FAILURE,
            .instance = "/*? instance ?*/",
            .interface = "/*? interface ?*/",
            .description = "out of memory while unmarshalling /*? p.name ?*/ in /*? name ?*/",
            .alloc_bytes = sizeof(char*) * (* /*? p.name ?*/_sz),
          }), ({
            /*- for q in input_parameters -*/
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
            /*- for q in input_parameters -*/
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
          }));
      /*- endif -*/
      /*- if isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
        /*- set lcount = c_symbol() -*/
        for (int /*? lcount ?*/ = 0; /*? lcount ?*/ < * /*? p.name ?*/_sz; /*? lcount ?*/ ++) {
          /*- set len = c_symbol('strlen') -*/
          size_t /*? len ?*/ = strnlen(/*? base ?*/ + /*? length ?*/, /*? size ?*/ - /*? length ?*/);
          ERR_IF(/*? len ?*/ >= /*? size ?*/ - /*? length ?*/, /*? error_handler ?*/, ((camkes_error_t){
              .type = CE_MALFORMED_RPC_PAYLOAD,
              .instance = "/*? instance ?*/",
              .interface = "/*? interface ?*/",
              .description = "truncated message encountered while unmarshalling /*? p.name ?*/ in /*? name ?*/",
              .length = /*? size ?*/,
              .current_index = /*? length ?*/ + /*? len ?*/ + 1,
            }), ({
              /*- for q in input_parameters -*/
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
              /*- set mcount = c_symbol() -*/
              for (int /*? mcount ?*/ = 0; /*? mcount ?*/ < /*? lcount ?*/; /*? mcount ?*/ ++) {
                free((* /*? p.name ?*/)[/*? mcount ?*/]);
              }
              free(* /*? p.name ?*/);
              return -1;
            }));
          /* If we didn't trigger an error, we now know this strdup is safe. */
          (* /*? p.name ?*/)[/*? lcount ?*/] = strdup(/*? base ?*/ + /*? length ?*/);
          ERR_IF((* /*? p.name ?*/)[/*? lcount ?*/] == NULL, /*? error_handler ?*/, ((camkes_error_t){
              .type = CE_ALLOCATION_FAILURE,
              .instance = "/*? instance ?*/",
              .interface = "/*? interface ?*/",
              .description = "out of memory while unmarshalling /*? p.name ?*/ in /*? name ?*/",
              .alloc_bytes = /*? len ?*/ + 1,
            }), ({
              /*- for q in input_parameters -*/
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
              /*- set mcount = c_symbol() -*/
              for (int /*? mcount ?*/ = 0; /*? mcount ?*/ < /*? lcount ?*/; /*? mcount ?*/ ++) {
                free((* /*? p.name ?*/)[/*? mcount ?*/]);
              }
              free(* /*? p.name ?*/);
              return -1;
            }));
          /*? length ?*/ += /*? len ?*/ + 1;
        }
      /*- else -*/
        ERR_IF(/*? length ?*/ + sizeof((* /*? p.name ?*/)[0]) * (* /*? p.name ?*/_sz) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
            .type = CE_MALFORMED_RPC_PAYLOAD,
            .instance = "/*? instance ?*/",
            .interface = "/*? interface ?*/",
            .description = "truncated message encountered while unmarshalling /*? p.name ?*/ in /*? name ?*/",
            .length = /*? size ?*/,
            .current_index = /*? length ?*/ + sizeof((* /*? p.name ?*/)[0]) * (* /*? p.name ?*/_sz),
          }), ({
            /*- for q in input_parameters -*/
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
            free(* /*? p.name ?*/);
            return -1;
          }));
        memcpy((* /*? p.name ?*/), /*? base ?*/ + /*? length ?*/, sizeof((* /*? p.name ?*/)[0]) * (* /*? p.name ?*/_sz));
        /*? length ?*/ += sizeof((* /*? p.name ?*/)[0]) * (* /*? p.name ?*/_sz);
      /*- endif -*/
    /*- elif isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
      /*- set len = c_symbol('strlen') -*/
      size_t /*? len ?*/ = strnlen(/*? base ?*/ + /*? length ?*/, /*? size ?*/ - /*? length ?*/);
      ERR_IF(/*? len ?*/ >= /*? size ?*/ - /*? length ?*/, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_MALFORMED_RPC_PAYLOAD,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "truncated message encountered while unmarshalling /*? p.name ?*/ in /*? name ?*/",
          .length = /*? size ?*/,
          .current_index = /*? length ?*/ + /*? len ?*/ + 1,
        }), ({
          /*- for q in input_parameters -*/
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
        }));
      * /*? p.name ?*/ = strdup(/*? base ?*/ + /*? length ?*/);
      ERR_IF(* /*? p.name ?*/ == NULL, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_ALLOCATION_FAILURE,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "out of memory while unmarshalling /*? p.name ?*/ in /*? name ?*/",
          .alloc_bytes = /*? len ?*/ + 1,
        }), ({
          /*- for q in input_parameters -*/
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
        }));
      /*? length ?*/ += /*? len ?*/ + 1;
    /*- else -*/
      ERR_IF(/*? length ?*/ + sizeof(* /*? p.name ?*/) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_MALFORMED_RPC_PAYLOAD,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "truncated message encountered while unmarshalling /*? p.name ?*/ in /*? name ?*/",
          .length = /*? size ?*/,
          .current_index = /*? length ?*/ + sizeof(* /*? p.name ?*/),
        }), ({
          /*- for q in input_parameters -*/
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
        }));
      memcpy(/*? p.name ?*/, /*? base ?*/ + /*? length ?*/, sizeof(* /*? p.name ?*/));
      /*? length ?*/ += sizeof(* /*? p.name ?*/);
    /*- endif -*/
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
        /*- for p in input_parameters -*/
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
