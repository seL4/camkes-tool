/*# We expect the following variables to be defined when this fragment is
 *# included.
 #*/
/*? assert(isinstance(name, str)) ?*/          /*# Name of this component instance #*/
/*? assert(isinstance(function, str)) ?*/      /*# Name of function to create #*/
/*? assert(isinstance(buffer, str)) ?*/        /*# Buffer symbol (or expression) to marshal into #*/
/*? assert(isinstance(size, str)) ?*/          /*# Length of the buffer; possibly not generation-time constant #*/
/*? assert(isinstance(method_index, int)) ?*/  /*# Index of this method in the containing interface #*/
/*? assert(isinstance(methods_len, int)) ?*/   /*# Total number of methods in this interface #*/
/*? assert(isinstance(input_parameters, list)) ?*/   /*# All input parameters to this method #*/

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
    memcpy(/*? base ?*/, & /*? call ?*/, sizeof(/*? call ?*/));
    /*? length ?*/ += sizeof(/*? call ?*/);
  /*- endif -*/
  
  /* Marshal the parameters. */
  /*- for p in input_parameters -*/
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
    "buffer length exceeded while marshalling inputs for /*? name ?*/");

  return /*? length ?*/;
}
