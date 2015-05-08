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

(** TPP: condense = True *)
definition ipc_buffer :: "string \<Rightarrow> nat \<Rightarrow> cdl_object_id option"
  where "ipc_buffer name index \<equiv>
  /*- set tcbs = {} -*/
  /*- set to_unfold = set() -*/
  /*- for i in composition.instances -*/
    /*- do tcbs.__setitem__('%s_tcb__control' % i.name, (i.name, 0)) -*/
    /*- for index, inf in enumerate(i.type.provides + i.type.uses + i.type.emits + i.type.consumes + i.type.dataports) -*/
      /*- do tcbs.__setitem__('%s_tcb_%s' % (i.name, inf.name), (i.name, index + 1)) -*/
    /*- endfor -*/
  /*- endfor -*/
  /*- for o in obj_space.spec.objs -*/
    /*- if o.name is not none and o.name in tcbs -*/
      if name = ''/*? tcbs[o.name][0] ?*/'' \<and> index = /*? tcbs[o.name][1] ?*/ then Some /*? o['ipc_buffer_slot'].referent.name ?*/_id else
      /*- do to_unfold.add('%s_id_def' % o['ipc_buffer_slot'].referent.name) -*/
    /*- endif -*/
  /*- endfor -*/
      None
  "
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma buffers_distinct:
  "\<And>n i m j. \<exists>f. ipc_buffer n i = Some f \<and> ipc_buffer m j = Some f \<Longrightarrow> n = m \<and> i = j"
  apply (unfold ipc_buffer_def /*? ' '.join(to_unfold) ?*/)
  /*- for a in tcbs.values() -*/
  apply (case_tac "n = ''/*? a[0] ?*/'' \<and> i = /*? a[1] ?*/")
    /*- for b in tcbs.values() -*/
   apply (case_tac "m = ''/*? b[0] ?*/'' \<and> j = /*? b[1] ?*/")
    apply clarsimp
    /*- endfor -*/
   apply auto[1]
  /*- endfor -*/
  by auto[1]
(** TPP: condense = False *)

end
