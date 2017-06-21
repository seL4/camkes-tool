/*
 * Copyright 2017, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 */

/*# We expect the following variables to be defined when this fragment is
 *# included.
 #*/
/*? assert(isinstance(function, six.string_types)) ?*/      /*# Name of function to create #*/
/*? assert(isinstance(size, six.string_types)) ?*/          /*# Name of a variable storing the byte length of the message #*/
/*? assert(isinstance(output_parameters, (list, tuple))) ?*/   /*# All output parameters to this method #*/
/*? assert(return_type is none or isinstance(return_type, six.string_types)) ?*/
                                               /*# Return type of this interface #*/
/*# ret_ptr #*/                                /*# Pointer for the return value #*/

/*? function ?*/(
/*? size ?*/
/*- if return_type is not none or len(output_parameters) > 0 -*/
  ,
/*- endif -*/
/*- if return_type is not none -*/
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
