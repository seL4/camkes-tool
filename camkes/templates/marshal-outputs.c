/*# We expect the following variables to be defined when this fragment is
 *# included.
 #*/
/*? assert(isinstance(instance, str)) ?*/      /*# Name of this component instance #*/
/*? assert(isinstance(interface, str)) ?*/     /*# Name of this interface #*/
/*? assert(isinstance(name, str)) ?*/          /*# Name of this method #*/
/*? assert(isinstance(function, str)) ?*/      /*# Name of function to create #*/
/*? assert(isinstance(buffer, str)) ?*/        /*# Buffer symbol (or expression) to marshal into #*/
/*? assert(isinstance(size, str)) ?*/          /*# Length of the buffer; possibly not generation-time constant #*/
/*? assert(isinstance(output_parameters, list)) ?*/   /*# All output parameters to this method #*/
/*? assert(return_type == None or isinstance(return_type, camkes.ast.Type) or isinstance(return_type, camkes.ast.Reference)) ?*/
                                               /*# Return type of this interface #*/
/*? assert(isinstance(error_handler, str)) ?*/ /*# Handler to invoke on error #*/

static unsigned int /*? function ?*/(
/*- set ret = c_symbol('return') -*/
/*- if return_type -*/
  /*- if return_type.array -*/
    size_t /*? ret ?*/_sz,
    /*- if isinstance(return_type, camkes.ast.Type) and return_type.type == 'string' -*/
      char ** /*? ret ?*/
    /*- else -*/
      /*? show(return_type) ?*/ * /*? ret ?*/
    /*- endif -*/
  /*- elif isinstance(return_type, camkes.ast.Type) and return_type.type == 'string' -*/
    char * /*? ret ?*/
  /*- else -*/
    /*? show(return_type) ?*/ /*? ret ?*/
  /*- endif -*/
  /*- if len(output_parameters) > 0 -*/
    ,
  /*- endif -*/
/*- endif -*/
/*- for p in output_parameters -*/
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

  /*- if return_type -*/
    /* Marshal the return value. */
    /*- if return_type.array -*/
      ERR_IF(/*? length ?*/ + sizeof(/*? ret ?*/_sz) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_BUFFER_LENGTH_EXCEEDED,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "buffer exceeded while marshalling return value for /*? name ?*/",
          .current_length = /*? length ?*/,
          .target_length = /*? length ?*/ + sizeof(/*? ret ?*/_sz),
        }), ({
          return UINT_MAX;
        }));
      memcpy(/*? base ?*/ + /*? length ?*/, & /*? ret ?*/_sz, sizeof(/*? ret ?*/_sz));
      /*? length ?*/ += sizeof(/*? ret ?*/_sz);
      /*- set lcount = c_symbol() -*/
      for (int /*? lcount ?*/ = 0; /*? lcount ?*/ < /*? ret ?*/_sz; /*? lcount ?*/ ++) {
        /*- if isinstance(return_type, camkes.ast.Type) and return_type.type == 'string' -*/
          /*- set len = c_symbol('strlen') -*/
          size_t /*? len ?*/ = strnlen(/*? ret ?*/[/*? lcount ?*/], /*? size ?*/ - /*? length ?*/);
          ERR_IF(/*? len ?*/ >= /*? size ?*/ - /*? length ?*/, /*? error_handler ?*/, ((camkes_error_t){
              .type = CE_BUFFER_LENGTH_EXCEEDED,
              .instance = "/*? instance ?*/",
              .interface = "/*? interface ?*/",
              .description = "buffer exceeded while marshalling return value for /*? name ?*/",
              .current_length = /*? length ?*/,
              .target_length = /*? length ?*/ + /*? len ?*/ + 1,
            }), ({
              return UINT_MAX;
            }));
          /* If we didn't trigger an error, we now know this strcpy is safe. */
          (void)strcpy(/*? base ?*/ + /*? length ?*/, /*? ret ?*/[/*? lcount ?*/]);
          /*? length ?*/ += /*? len ?*/ + 1;
        /*- else -*/
          ERR_IF(/*? length ?*/ + sizeof(/*? ret ?*/[0]) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
              .type = CE_BUFFER_LENGTH_EXCEEDED,
              .instance = "/*? instance ?*/",
              .interface = "/*? interface ?*/",
              .description = "buffer exceeded while marshalling return value for /*? name ?*/",
              .current_length = /*? length ?*/,
              .target_length = /*? length ?*/ + sizeof(/*? ret ?*/[0]),
            }), ({
              return UINT_MAX;
            }));
          memcpy(/*? base ?*/ + /*? length ?*/, /*? ret ?*/ + /*? lcount ?*/, sizeof(/*? ret ?*/[0]));
          /*? length ?*/ += sizeof(/*? ret ?*/[0]);
        /*- endif -*/
      }
    /*- elif isinstance(return_type, camkes.ast.Type) and return_type.type == 'string' -*/
      /*- set len = c_symbol('strlen') -*/
      size_t /*? len ?*/ = strnlen(/*? ret ?*/, /*? size ?*/ - /*? length ?*/);
      ERR_IF(/*? len ?*/ >= /*? size ?*/ - /*? length ?*/, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_BUFFER_LENGTH_EXCEEDED,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "buffer exceeded while marshalling return value for /*? name ?*/",
          .current_length = /*? length ?*/,
          .target_length = /*? length ?*/ + /*? len ?*/ + 1,
        }), ({
          return UINT_MAX;
        }));
      /* If we didn't trigger an error, we now know this strcpy is safe. */
      (void)strcpy(/*? base ?*/ + /*? length ?*/, /*? ret ?*/);
      /*? length ?*/ += /*? len ?*/ + 1;
    /*- else -*/
      ERR_IF(/*? length ?*/ + sizeof(/*? ret ?*/) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_BUFFER_LENGTH_EXCEEDED,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "buffer exceeded while marshalling return value for /*? name ?*/",
          .current_length = /*? length ?*/,
          .target_length = /*? length ?*/ + sizeof(/*? ret ?*/),
        }), ({
          return UINT_MAX;
        }));
      memcpy(/*? base ?*/ + /*? length ?*/, & /*? ret ?*/, sizeof(/*? ret ?*/));
      /*? length ?*/ += sizeof(/*? ret ?*/);
    /*- endif -*/
  /*- endif -*/
  
  /* Marshal output parameters. */
  /*- for p in output_parameters -*/
    /*? assert(isinstance(p.type, camkes.ast.Type) or isinstance(p.type, camkes.ast.Reference)) ?*/
    /*- if p.array -*/
      ERR_IF(/*? length ?*/ + sizeof(/*? p.name ?*/_sz) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_BUFFER_LENGTH_EXCEEDED,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "buffer exceeded while marshalling /*? p.name ?*/ in /*? name ?*/",
          .current_length = /*? length ?*/,
          .target_length = /*? length ?*/ + sizeof(/*? p.name ?*/_sz),
        }), ({
          return UINT_MAX;
        }));
      memcpy(/*? base ?*/ + /*? length ?*/, & /*? p.name ?*/_sz, sizeof(/*? p.name ?*/_sz));
      /*? length ?*/ += sizeof(/*? p.name ?*/_sz);
      /*- set lcount = c_symbol() -*/
      for (int /*? lcount ?*/ = 0; /*? lcount ?*/ < /*? p.name ?*/_sz; /*? lcount ?*/ ++) {
        /*- if isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
          /*- set len = c_symbol('strlen') -*/
          size_t /*? len ?*/ = strnlen(/*? p.name ?*/[/*? lcount ?*/], /*? size ?*/ - /*? length ?*/);
          ERR_IF(/*? len ?*/ >= /*? size ?*/ - /*? length ?*/, /*? error_handler ?*/, ((camkes_error_t){
              .type = CE_BUFFER_LENGTH_EXCEEDED,
              .instance = "/*? instance ?*/",
              .interface = "/*? interface ?*/",
              .description = "buffer exceeded while marshalling /*? p.name ?*/ in /*? name ?*/",
              .current_length = /*? length ?*/,
              .target_length = /*? length ?*/ + /*? len ?*/ + 1,
            }), ({
              return UINT_MAX;
            }));
          /* If we didn't trigger an error, we now know this strcpy is safe. */
          (void)strcpy(/*? base ?*/ + /*? length ?*/, /*? p.name ?*/[/*? lcount ?*/]);
          /*? length ?*/ += /*? len ?*/ + 1;
        /*- else -*/
          ERR_IF(/*? length ?*/ + sizeof(/*? p.name ?*/[0]) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
              .type = CE_BUFFER_LENGTH_EXCEEDED,
              .instance = "/*? instance ?*/",
              .interface = "/*? interface ?*/",
              .description = "buffer exceeded while marshalling /*? p.name ?*/ in /*? name ?*/",
              .current_length = /*? length ?*/,
              .target_length = /*? length ?*/ + sizeof(/*? p.name ?*/[0]),
            }), ({
              return UINT_MAX;
            }));
          memcpy(/*? base ?*/ + /*? length ?*/, /*? p.name ?*/ + /*? lcount ?*/, sizeof(/*? p.name ?*/[0]));
          /*? length ?*/ += sizeof(/*? p.name ?*/[0]);
        /*- endif -*/
      }
    /*- elif isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
      /*- set len = c_symbol('strlen') -*/
      size_t /*? len ?*/ = strnlen(/*? p.name ?*/, /*? size ?*/ - /*? length ?*/);
      ERR_IF(/*? len ?*/ >= /*? size ?*/ - /*? length ?*/, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_BUFFER_LENGTH_EXCEEDED,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "buffer exceeded while marshalling /*? p.name ?*/ in /*? name ?*/",
          .current_length = /*? length ?*/,
          .target_length = /*? length ?*/ + /*? len ?*/ + 1,
        }), ({
          return UINT_MAX;
        }));
      /* If we didn't trigger an error, we now know this strcpy is safe. */
      (void)strcpy(/*? base ?*/ + /*? length ?*/, /*? p.name ?*/);
      /*? length ?*/ += /*? len ?*/ + 1;
    /*- else -*/
      ERR_IF(/*? length ?*/ + sizeof(/*? p.name ?*/) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
          .type = CE_BUFFER_LENGTH_EXCEEDED,
          .instance = "/*? instance ?*/",
          .interface = "/*? interface ?*/",
          .description = "buffer exceeded while marshalling /*? p.name ?*/ in /*? name ?*/",
          .current_length = /*? length ?*/,
          .target_length = /*? length ?*/ + sizeof(/*? p.name ?*/),
        }), ({
          return UINT_MAX;
        }));
      memcpy(/*? base ?*/ + /*? length ?*/, & /*? p.name ?*/, sizeof(/*? p.name ?*/));
      /*? length ?*/ += sizeof(/*? p.name ?*/);
    /*- endif -*/
  /*- endfor -*/
  
  assert(/*? length ?*/ <= /*? size ?*/ &&
    "uncaught buffer overflow while marshalling outputs for /*? name ?*/");

  return /*? length ?*/;
}
