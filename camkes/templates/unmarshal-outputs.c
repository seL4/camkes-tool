/*# We expect the following variables to be defined when this fragment is
 *# included.
 #*/
/*? assert(isinstance(name, str)) ?*/          /*# Name of this component instance #*/
/*? assert(isinstance(function, str)) ?*/      /*# Name of function to create #*/
/*? assert(isinstance(buffer, str)) ?*/        /*# Buffer symbol (or expression) to marshal into #*/
/*? assert(isinstance(size, str)) ?*/          /*# Length of the buffer; possibly not generation-time constant #*/
/*? assert(isinstance(method_index, int)) ?*/  /*# Index of this method in the containing interface #*/
/*? assert(isinstance(output_parameters, list)) ?*/   /*# All output parameters to this method #*/
/*? assert(return_type == None or isinstance(return_type, camkes.ast.Type) or isinstance(return_type, camkes.ast.Reference)) ?*/
                                               /*# Return type of this interface #*/

static 
/*- if return_type -*/
  /*- if return_type.array -*/
    /*- if isinstance(return_type, camkes.ast.Type) and return_type.type == 'string' -*/
      char **
    /*- else -*/
      /*? show(return_type) ?*/ *
    /*- endif -*/
  /*- elif isinstance(return_type, camkes.ast.Type) and return_type.type == 'string' -*/
    char *
  /*- else -*/
    /*? show(return_type) ?*/
  /*- endif -*/
/*- else -*/
  void
/*- endif -*/
/*? function ?*/(
/*- set ret = c_symbol('return') -*/
/*- if return_type and return_type.array -*/
  size_t * /*? ret ?*/_sz,
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
      memcpy(/*? ret ?*/_sz, /*? base ?*/ + /*? length ?*/, sizeof(* /*? ret ?*/_sz));
      /*? length ?*/ += sizeof(* /*? ret ?*/_sz);
      /*- if isinstance(return_type, camkes.ast.Type) and return_type.type == 'string' -*/
        char ** /*? ret ?*/ = malloc(sizeof(char) * CAMKES_STR_MAX * (* /*? ret_sz ?*/));
        assert(/*? ret ?*/ != NULL);
      /*- else -*/
        /*? show(return_type) ?*/ * /*? ret ?*/ = malloc(sizeof(/*? ret ?*/[0]) * (* /*? ret_sz ?*/));
        assert(/*? ret ?*/ != NULL);
      /*- endif -*/
      /*- set lcount = c_symbol() -*/
      for (int /*? lcount ?*/ = 0; /*? lcount ?*/ < * /*? ret ?*/_sz; /*? lcount ?*/ ++) {
        /*- if isinstance(return_type, camkes.ast.Type) and return_type.type == 'string' -*/
          /*- set end = c_symbol() -*/
          char * /*? end ?*/ = stpcpy(/*? ret ?*/[/*? lcount ?*/], /*? base ?*/ + /*? length ?*/);
          /*? length ?*/ += (uintptr_t)/*? end ?*/ - ((uintptr_t)(/*? ret ?*/[/*? lcount ?*/]) + 1;
        /*- else -*/
          memcpy(/*? ret ?*/ + /*? lcount ?*/, /*? base ?*/ + /*? length ?*/, sizeof(/*? ret ?*/[0]));
          /*? length ?*/ += sizeof(/*? ret ?*/[0]);
        /*- endif -*/
      }
    /*- elif isinstance(return_type, camkes.ast.Type) and return_type.type == 'string' -*/
      char * /*? ret ?*/ = malloc(sizeof(char) * CAMKES_STR_MAX);
      assert(/*? ret ?*/ != NULL);
      /*- set end = c_symbol() -*/
      char * /*? end ?*/ = stpcpy(/*? ret ?*/, /*? base ?*/ + /*? length ?*/);
      /*? length ?*/ += (uintptr_t)/*? end ?*/ - ((uintptr_t)/*? ret ?*/) + 1;
    /*- else -*/
      /*? show(return_type) ?*/ /*? ret ?*/;
      memcpy(& /*? ret ?*/, /*? base ?*/ + /*? length ?*/, sizeof(/*? ret ?*/));
      /*? length ?*/ += sizeof(/*? ret ?*/);
    /*- endif -*/
  /*- endif -*/
  
  /* Unmarshal the parameters. */
  /*- for p in output_parameters -*/
    /*? assert(isinstance(p.type, camkes.ast.Type) or isinstance(p.type, camkes.ast.Reference)) ?*/
    /*- if p.array -*/
      memcpy(/*? p.name ?*/_sz, /*? base ?*/ + /*? length ?*/, sizeof(* /*? p.name ?*/_sz));
      /*? length ?*/ += sizeof(* /*? p.name ?*/_sz);
      /*- if p.direction.direction == 'inout' -*/
        free(* /*? p.name ?*/);
      /*- endif -*/
      /*- if isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
        * /*? p.name ?*/ = malloc(sizeof(char) * CAMKES_STR_MAX * (* /*? p.name ?*/_sz));
        assert(* /*? p.name ?*/ != NULL);
      /*- else -*/
        * /*? p.name ?*/ = malloc(sizeof((* /*? p.name ?*/)[0]) * (* /*? p.name ?*/_sz));
        assert(* /*? p.name ?*/ != NULL);
      /*- endif -*/
      /*- set lcount = c_symbol() -*/
      for (int /*? lcount ?*/ = 0; /*? lcount ?*/ < * /*? p.name ?*/_sz; /*? lcount ?*/ ++) {
        /*- if isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
          /*- set end = c_symbol() -*/
          char * /*? end ?*/ = stpcpy((* /*? p.name ?*/)[/*? lcount ?*/], /*? base ?*/ + /*? length ?*/);
          /*? length ?*/ += (uintptr_t)/*? end ?*/ - (uintptr_t)((* /*? p.name ?*/)[/*? lcount ?*/]) + 1;
        /*- else -*/
          memcpy((* /*? p.name ?*/) + /*? lcount ?*/, /*? base ?*/ + /*? length ?*/, sizeof((* /*? p.name ?*/)[0]));
          /*? length ?*/ += sizeof((* /*? p.name ?*/)[0]);
        /*- endif -*/
      }
    /*- elif isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
      /*- if p.direction.direction == 'inout' -*/
        free(* /*? p.name ?*/);
      /*- endif -*/
      * /*? p.name ?*/ = malloc(sizeof(char) * CAMKES_STR_MAX);
      assert(* /*? p.name ?*/ != NULL);
      /*- set end = c_symbol() -*/
      char * /*? end ?*/ = stpcpy(* /*? p.name ?*/, /*? base ?*/ + /*? length ?*/);
      /*? length ?*/ += (uintptr_t)/*? end ?*/ - (uintptr_t)(* /*? p.name ?*/) + 1;
    /*- else -*/
      memcpy(/*? p.name ?*/, /*? base ?*/ + /*? length ?*/, sizeof(* /*? p.name ?*/));
      /*? length ?*/ += sizeof(* /*? p.name ?*/);
    /*- endif -*/
  /*- endfor -*/
  
  assert(/*? length ?*/ <= /*? size ?*/ &&
    "buffer length exceeded while unmarshalling outputs for /*? name ?*/");

  /*- if return_type -*/
    return /*? ret ?*/;
  /*- endif -*/
}
