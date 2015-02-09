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
    /* Unmarshal the return value. */
    /*- if return_type.array -*/
      ERR_IF(/*? length ?*/ + sizeof(* /*? ret ?*/_sz) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_MALFORMED_RPC_PAYLOAD,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "truncated message encountered while unmarshalling return value for /*? name ?*/",
          .length = /*? size ?*/,
          .current_index = /*? length ?*/ + sizeof(* /*? ret ?*/_sz),
        }), ({
          return -1;
        }));
      memcpy(/*? ret ?*/_sz, /*? base ?*/ + /*? length ?*/, sizeof(* /*? ret ?*/_sz));
      /*? length ?*/ += sizeof(* /*? ret ?*/_sz);
      /*- if isinstance(return_type, camkes.ast.Type) and return_type.type == 'string' -*/
        * /*? ret ?*/ = malloc(sizeof(char*) * (* /*? ret ?*/_sz));
        ERR_IF(* /*? ret ?*/ == NULL, /*? error_handler ?*/, ((camkes_error_t){
            .type = CE_ALLOCATION_FAILURE,
            .instance = "/*? instance ?*/",
            .interface = "/*? interface ?*/",
            .description = "out of memory while unmarshalling return value for /*? name ?*/",
            .alloc_bytes = sizeof(char*) * (* /*? ret ?*/_sz),
          }), ({
            return -1;
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
            return -1;
          }));
      /*- endif -*/
      /*- set lcount = c_symbol() -*/
      for (int /*? lcount ?*/ = 0; /*? lcount ?*/ < * /*? ret ?*/_sz; /*? lcount ?*/ ++) {
        /*- if isinstance(return_type, camkes.ast.Type) and return_type.type == 'string' -*/
          /*- set len = c_symbol('strlen') -*/
          size_t /*? len ?*/ = strnlen(/*? base ?*/ + /*? length ?*/, /*? size ?*/ - /*? length ?*/);
          ERR_IF(/*? len ?*/ >= /*? size ?*/ - /*? length ?*/, /*? error_handler ?*/, ((camkes_error_t){
              .type = CE_MALFORMED_RPC_PAYLOAD,
              .instance = "/*? instance ?*/",
              .interface = "/*? interface ?*/",
              .description = "truncated message encountered while unmarshalling return value for /*? name ?*/",
              .length = /*? size ?*/,
              .current_index = /*? length ?*/ + /*? len ?*/ + 1,
            }), ({
              /*- set mcount = c_symbol() -*/
              for (int /*? mcount ?*/ = 0; /*? mcount ?*/ < /*? lcount ?*/; /*? mcount ?*/ ++) {
                free((* /*? ret ?*/)[/*? mcount ?*/]);
              }
              free(* /*? ret ?*/);
              return -1;
            }));
          /* If we didn't trigger an error, we now know this strdup is safe. */
          (* /*? ret ?*/)[/*? lcount ?*/] = strdup(/*? base ?*/ + /*? length ?*/);
          ERR_IF((* /*? ret ?*/)[/*? lcount ?*/] == NULL, /*? error_handler ?*/, ((camkes_error_t){
              .type = CE_ALLOCATION_FAILURE,
              .instance = "/*? instance ?*/",
              .interface = "/*? interface ?*/",
              .description = "out of memory while unmarshalling return value for /*? name ?*/",
              .alloc_bytes = /*? len ?*/ + 1,
            }), ({
              /*- set mcount = c_symbol() -*/
              for (int /*? mcount ?*/ = 0; /*? mcount ?*/ < /*? lcount ?*/; /*? mcount ?*/ ++) {
                free((* /*? ret ?*/)[/*? mcount ?*/]);
              }
              free(* /*? ret ?*/);
              return -1;
            }));

          /*? length ?*/ += /*? len ?*/ + 1;
        /*- else -*/
          ERR_IF(/*? length ?*/ + sizeof((* /*? ret ?*/)[0]) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
              .type = CE_MALFORMED_RPC_PAYLOAD,
              .instance = "/*? instance ?*/",
              .interface = "/*? interface ?*/",
              .description = "truncated message encountered while unmarshalling return value for /*? name ?*/",
              .length = /*? size ?*/,
              .current_index = /*? length ?*/ + sizeof((* /*? ret ?*/)[0]),
            }), ({
              free(* /*? ret ?*/);
              return -1;
            }));
          memcpy((* /*? ret ?*/) + /*? lcount ?*/, /*? base ?*/ + /*? length ?*/, sizeof((* /*? ret ?*/)[0]));
          /*? length ?*/ += sizeof((* /*? ret ?*/[0]));
        /*- endif -*/
      }
    /*- elif isinstance(return_type, camkes.ast.Type) and return_type.type == 'string' -*/
      /*- set len = c_symbol('strlen') -*/
      size_t /*? len ?*/ = strnlen(/*? base ?*/ + /*? length ?*/, /*? size ?*/ - /*? length ?*/);
      ERR_IF(/*? len ?*/ >= /*? size ?*/ - /*? length ?*/, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_MALFORMED_RPC_PAYLOAD,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "truncated message encountered while unmarshalling return value for /*? name ?*/",
          .length = /*? size ?*/,
          .current_index = /*? length ?*/ + /*? len ?*/ + 1,
        }), ({
          return -1;
        }));
      * /*? ret ?*/ = strdup(/*? base ?*/ + /*? length ?*/);
      ERR_IF(* /*? ret ?*/ == NULL, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_ALLOCATION_FAILURE,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "out of memory while unmarshalling return value for /*? name ?*/",
          .alloc_bytes = /*? len ?*/ + 1,
        }), ({
          return -1;
        }));
      /*? length ?*/ += /*? len ?*/ + 1;
    /*- else -*/
      ERR_IF(/*? length ?*/ + sizeof(* /*? ret ?*/) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_MALFORMED_RPC_PAYLOAD,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "truncated message encountered while unmarshalling return value for /*? name ?*/",
          .length = /*? size ?*/,
          .current_index = /*? length ?*/ + sizeof(* /*? ret ?*/),
        }), ({
          return -1;
        }));
      memcpy(/*? ret ?*/, /*? base ?*/ + /*? length ?*/, sizeof(* /*? ret ?*/));
      /*? length ?*/ += sizeof(* /*? ret ?*/);
    /*- endif -*/
  /*- endif -*/
  
  /* Unmarshal the parameters. */
  /*- for p in output_parameters -*/
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
        }));
      memcpy(/*? p.name ?*/_sz, /*? base ?*/ + /*? length ?*/, sizeof(* /*? p.name ?*/_sz));
      /*? length ?*/ += sizeof(* /*? p.name ?*/_sz);
      /*- if p.direction.direction == 'inout' -*/
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
          }));
      /*- endif -*/
      /*- set lcount = c_symbol() -*/
      for (int /*? lcount ?*/ = 0; /*? lcount ?*/ < * /*? p.name ?*/_sz; /*? lcount ?*/ ++) {
        /*- if isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
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
              /*- set mcount = c_symbol() -*/
              for (int /*? mcount ?*/ = 0; /*? mcount ?*/ < /*? lcount ?*/; /*? mcount ?*/ ++) {
                free((* /*? p.name ?*/)[/*? mcount ?*/]);
              }
              free(* /*? p.name ?*/);
              return -1;
            }));
          /*? length ?*/ += /*? len ?*/ + 1;
        /*- else -*/
          ERR_IF(/*? length ?*/ + sizeof((* /*? p.name ?*/)[0]) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
              .type = CE_MALFORMED_RPC_PAYLOAD,
              .instance = "/*? instance ?*/",
              .interface = "/*? interface ?*/",
              .description = "truncated message encountered while unmarshalling /*? p.name ?*/ in /*? name ?*/",
              .length = /*? size ?*/,
              .current_index = /*? length ?*/ + sizeof((* /*? p.name ?*/)[0]),
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
              free(* /*? p.name ?*/);
              return -1;
            }));
          memcpy((* /*? p.name ?*/) + /*? lcount ?*/, /*? base ?*/ + /*? length ?*/, sizeof((* /*? p.name ?*/)[0]));
          /*? length ?*/ += sizeof((* /*? p.name ?*/)[0]);
        /*- endif -*/
      }
    /*- elif isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
      /*- if p.direction.direction == 'inout' -*/
        free(* /*? p.name ?*/);
      /*- endif -*/
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
        }));
      * /*? p.name ?*/ = strdup(/*? base ?*/ + /*? length ?*/);
      ERR_IF(* /*? p.name ?*/ == NULL, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_ALLOCATION_FAILURE,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "out of memory while unmarshalling /*? p.name ?*/ in /*? name ?*/",
          .alloc_bytes = /*? len ?*/ + 1,
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
