/*# We expect the following variables to be defined when this fragment is
 *# included.
 #*/
/*? assert(isinstance(name, str)) ?*/          /*# Name of this component instance #*/
/*? assert(isinstance(function, str)) ?*/      /*# Name of function to create #*/
/*? assert(isinstance(buffer, str)) ?*/        /*# Buffer symbol (or expression) to marshal into #*/
/*? assert(isinstance(size, str)) ?*/          /*# Length of the buffer; possibly not generation-time constant #*/
/*? assert(isinstance(output_parameters, list)) ?*/   /*# All output parameters to this method #*/
/*? assert(return_type == None or isinstance(return_type, camkes.ast.Type) or isinstance(return_type, camkes.ast.Reference)) ?*/
                                               /*# Return type of this interface #*/

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
      memcpy(/*? base ?*/ + /*? length ?*/, & /*? ret ?*/_sz, sizeof(/*? ret ?*/_sz));
      /*? length ?*/ += sizeof(/*? ret ?*/_sz);
      /*- set lcount = c_symbol() -*/
      for (int /*? lcount ?*/ = 0; /*? lcount ?*/ < /*? ret ?*/_sz; /*? lcount ?*/ ++) {
        /*- if isinstance(return_type, camkes.ast.Type) and return_type.type == 'string' -*/
          /*- set end = c_symbol() -*/
          char * /*? end ?*/ = stpcpy(/*? base ?*/ + /*? length ?*/, /*? ret ?*/[/*? lcount ?*/]);
          /*? length ?*/ += (uintptr_t)/*? end ?*/ - ((uintptr_t)(/*? base ?*/ + /*? length ?*/)) + 1;
        /*- else -*/
          memcpy(/*? base ?*/ + /*? length ?*/, /*? ret ?*/ + /*? lcount ?*/, sizeof(/*? ret ?*/[0]));
          /*? length ?*/ += sizeof(/*? ret ?*/[0]);
        /*- endif -*/
      }
    /*- elif isinstance(return_type, camkes.ast.Type) and return_type.type == 'string' -*/
      /*- set end = c_symbol() -*/
      char * /*? end ?*/ = stpcpy(/*? base ?*/ + /*? length ?*/, /*? ret ?*/);
      /*? length ?*/ += (uintptr_t)/*? end ?*/ - ((uintptr_t)(/*? base ?*/ + /*? length ?*/)) + 1;
    /*- else -*/
      memcpy(/*? base ?*/ + /*? length ?*/, & /*? ret ?*/, sizeof(/*? ret ?*/));
      /*? length ?*/ += sizeof(/*? ret ?*/);
    /*- endif -*/
  /*- endif -*/
  
  /* Marshal output parameters. */
  /*- for p in output_parameters -*/
    /*? assert(isinstance(p.type, camkes.ast.Type) or isinstance(p.type, camkes.ast.Reference)) ?*/
    /*- if p.array -*/
      memcpy(/*? base ?*/ + /*? length ?*/, & /*? p.name ?*/_sz, sizeof(/*? p.name ?*/_sz));
      /*? length ?*/ += sizeof(/*? p.name ?*/_sz);
      /*- set lcount = c_symbol() -*/
      for (int /*? lcount ?*/ = 0; /*? lcount ?*/ < /*? p.name ?*/_sz; /*? lcount ?*/ ++) {
        /*- if isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
          /*- set end = c_symbol() -*/
          char * /*? end ?*/ = stpcpy(/*? base ?*/ + /*? length ?*/, /*? p.name ?*/[/*? lcount ?*/]);
          /*? length ?*/ += (uintptr_t)/*? end ?*/ - ((uintptr_t)(/*? base ?*/ + /*? length ?*/)) + 1;
        /*- else -*/
          memcpy(/*? base ?*/ + /*? length ?*/, /*? p.name ?*/ + /*? lcount ?*/, sizeof(/*? p.name ?*/[0]));
          /*? length ?*/ += sizeof(/*? p.name ?*/[0]);
        /*- endif -*/
      }
    /*- elif isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
      /*- set end = c_symbol() -*/
      char * /*? end ?*/ = stpcpy(/*? base ?*/ + /*? length ?*/, /*? p.name ?*/);
      /*? length ?*/ += (uintptr_t)/*? end ?*/ - ((uintptr_t)(/*? base ?*/ + /*? length ?*/)) + 1;
    /*- else -*/
      memcpy(/*? base ?*/ + /*? length ?*/, & /*? p.name ?*/, sizeof(/*? p.name ?*/));
      /*? length ?*/ += sizeof(/*? p.name ?*/);
    /*- endif -*/
  /*- endfor -*/
  
  assert(/*? length ?*/ <= /*? size ?*/ &&
    "buffer length exceeded while marshalling outputs for /*? name ?*/");

  return /*? length ?*/;
}
