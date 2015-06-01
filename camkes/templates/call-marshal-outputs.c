/*# We expect the following variables to be defined when this fragment is
 *# included.
 #*/
/*? assert(isinstance(function, basestring)) ?*/      /*# Name of function to create #*/
/*? assert(isinstance(output_parameters, list)) ?*/   /*# All output parameters to this method #*/
/*? assert(return_type == None or isinstance(return_type, camkes.ast.Type) or isinstance(return_type, camkes.ast.Reference)) ?*/
                                               /*# Return type of this interface #*/
/*# ret_ptr #*/                                /*# Symbol for a pointer to the return value #*/

/*? function ?*/(
/*- if return_type is not none -*/
  /*? assert(isinstance(ret_ptr, basestring)) ?*/
  /*? ret_ptr ?*/
  /*- if len(output_parameters) > 0 -*/
    ,
  /*- endif -*/
/*- endif -*/
/*- for p in output_parameters -*/
  /*- if p.array -*/
    /*? p.name ?*/_sz_ptr,
  /*- endif -*/
  /*? p.name ?*/_ptr
  /*- if not loop.last -*/
    ,
  /*- endif -*/
/*- endfor -*/
)
