/*# We expect the following variables to be defined when this fragment is
 *# included.
 #*/
/*? assert(isinstance(function, str)) ?*/      /*# Name of function to create #*/
/*? assert(isinstance(input_parameters, list)) ?*/   /*# All input parameters to this method #*/

/*? function ?*/(
/*- for p in input_parameters -*/
  /*- if p.direction.direction == 'in' -*/
    /*- if p.array -*/
      /*? p.name ?*/_sz,
    /*- endif -*/
    /*? p.name ?*/
  /*- else -*/
    /*? assert(p.direction.direction == 'inout') ?*/
    /*- if p.array -*/
      * /*? p.name ?*/_sz,
      * /*? p.name ?*/
    /*- else -*/
      * /*? p.name ?*/
    /*- endif -*/
  /*- endif -*/
  /*- if not loop.last -*/
    ,
  /*- endif -*/
/*- endfor -*/
)
