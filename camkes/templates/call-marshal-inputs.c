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
/*? assert(isinstance(function, six.string_types)) ?*/     /*# Name of function to create #*/
/*? assert(isinstance(input_parameters, (list, tuple))) ?*/   /*# All input parameters to this method #*/

/*? function ?*/(
/*- for p in input_parameters -*/
  /*- if p.array -*/
    /*? p.name ?*/_sz,
  /*- endif -*/
  /*? p.name ?*/
  /*- if not loop.last -*/
    ,
  /*- endif -*/
/*- endfor -*/
)
