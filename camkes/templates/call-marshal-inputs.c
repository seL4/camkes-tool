/*# We expect the following variables to be defined when this fragment is
 *# included.
 #*/
/*? assert(isinstance(function, basestring)) ?*/     /*# Name of function to create #*/
/*? assert(isinstance(input_parameters, list)) ?*/   /*# All input parameters to this method #*/

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
