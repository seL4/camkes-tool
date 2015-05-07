/*#
 *# Copyright 2014, NICTA
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(NICTA_BSD)
 #*/

/*- set thy = splitext(os.path.basename(options.outfile.name))[0] -*/
theory /*? thy ?*/ imports
  CapDLSpec
begin

(** TPP: condense = True *)
datatype label
/*- set j = joiner('|') -*/
/*- for l in obj_space.labels -*/
  /*- if loop.first -*/=/*- endif -*//*? j() ?*/ /*? l ?*/
/*- endfor -*/
(** TPP: condense = False *)


(** TPP: condense = True *)
definition label_of :: "cdl_object_id \<Rightarrow> label option"
  where "label_of \<equiv> empty
  /*- for label, objs in obj_space.labels.items() -*/
    /*- for o in  objs -*/
      (/*? o.name ?*/_id \<mapsto> /*? label ?*/)
    /*- endfor -*/
  /*- endfor -*/
  "
(** TPP: condense = False *)

(** TPP: condense = True *)
definition id_of :: "string \<Rightarrow> cdl_object_id option"
  where "id_of name \<equiv>
  /*- for obj in obj_space.spec.objs -*/
    /*- if obj.name is not none -*/
      if name = ''/*? obj.name ?*/'' then Some /*? obj.name ?*/_id else
    /*- endif -*/
  /*- endfor -*/
      None"
(** TPP: condense = False *)

end
