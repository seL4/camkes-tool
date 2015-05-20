/*# We expect the following variables to be defined when this fragment is
 *# included.
 #*/
/*? assert(isinstance(function, basestring)) ?*/      /*# Name of function to create #*/
/*? assert(isinstance(size, basestring)) ?*/          /*# Name of a variable storing the byte length of the message #*/
/*? assert(isinstance(output_parameters, list)) ?*/   /*# All output parameters to this method #*/
/*? assert(return_type == None or isinstance(return_type, camkes.ast.Type) or isinstance(return_type, camkes.ast.Reference)) ?*/
                                               /*# Return type of this interface #*/
/*# ret_ptr #*/                                /*# Pointer for the return value #*/
/*# ret_sz #*/                                 /*# Symbol for the size of the return if it is an array #*/

/*? function ?*/(
/*? size ?*/
/*- if return_type or len(output_parameters) > 0 -*/
  ,
/*- endif -*/
/*- if return_type is not none -*/
  /*- if return_type.array -*/
    /*? assert(isinstance(ret_sz, basestring)) ?*/
    /*? ret_sz ?*/,
  /*- endif -*/
  /*? ret_ptr ?*/
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
