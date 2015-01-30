/*# We expect the following variables to be defined when this fragment is
 *# included.
 #*/
/*? assert(isinstance(function, str)) ?*/      /*# Name of function to create #*/
/*? assert(isinstance(output_parameters, list)) ?*/   /*# All output parameters to this method #*/
/*? assert(return_type == None or isinstance(return_type, camkes.ast.Type) or isinstance(return_type, camkes.ast.Reference)) ?*/
                                               /*# Return type of this interface #*/
/*# ret #*/                                    /*# Symbol for the return value #*/
/*# ret_sz #*/                                 /*# Symbol for the size of the return if it is an array #*/

/*? function ?*/(
/*- if return_type -*/
  /*? assert(isinstance(ret, str)) ?*/
  /*- if return_type.array -*/
    /*? assert(isinstance(ret_sz, str)) ?*/
    /*? ret_sz ?*/,
  /*- endif -*/
  /*? ret ?*/
  /*- if len(output_parameters) > 0 -*/
    ,
  /*- endif -*/
/*- endif -*/
/*- for p in output_parameters -*/
  /*- if p.array -*/
    /*? p.name ?*/_sz,
  /*- endif -*/
  /*? p.name ?*/
  /*- if not loop.last -*/
    ,
  /*- endif -*/
/*- endfor -*/
)
