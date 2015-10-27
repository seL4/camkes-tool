/*#
 *# Copyright 2015, NICTA
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(NICTA_BSD)
 #*/

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
