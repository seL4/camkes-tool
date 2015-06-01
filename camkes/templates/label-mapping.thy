/*#
 *# Copyright 2014, NICTA
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(NICTA_BSD)
 #*/

/*- set thy = os.path.splitext(os.path.basename(options.outfile.name))[0] -*/
theory /*? thy ?*/ imports
  "../../spec/capDL/CapDLSpec" (* generated *)
  Generator_CAMKES_CDL
  "../adl-spec/ArchSpec" (* generated *)
begin

/*# Ignore the comment below. It is intended to apply to the generated output,
 *# not this template.
 #*/
(* THIS THEORY IS GENERATED. DO NOT EDIT.
 * It is expected to be hosted in l4v/camkes/cdl-refine.
 *)

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

/*# We construct the proofs in this file as monolithic `by` invocations. This is
 *# horrible style, but in a large system the thousands of `apply` commands take
 *# a long time to process and hold up work on further proofs that depend on
 *# their results.
 #*/

(** TPP: condense = True *)
lemma ids_distinct': "\<And>n m. \<exists>i. id_of n = Some i \<and> id_of m = Some i \<Longrightarrow> n = m"
  /*- set to_unfold = set(['id_of_def']) -*/
  /*- for obj in obj_space.spec.objs -*/
    /*- if obj.name is not none -*/
      /*- do to_unfold.add('%s_id_def' % obj.name) -*/
    /*- endif -*/
  /*- endfor -*/
/*? '\n'.join(textwrap.wrap('  by (unfold %s,' % ' '.join(to_unfold), width=100, subsequent_indent=' ' * len('  by (unfold '))) ?*/
  /*- for n in obj_space.spec.objs -*/
    /*- if n.name is not none -*/
      case_tac "n = ''/*? n.name ?*/''",
      /*- for m in obj_space.spec.objs -*/
        /*- if m.name is not none -*/
       case_tac "m = ''/*? m.name ?*/''",
        clarsimp,
        /*- endif -*/
      /*- endfor -*/
       clarsimp,
    /*- endif -*/
  /*- endfor -*/
      clarsimp)
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
lemma buffers_distinct':
  "\<And>n i m j. \<exists>f. ipc_buffer n i = Some f \<and> ipc_buffer m j = Some f \<Longrightarrow> n = m \<and> i = j"
  by (unfold ipc_buffer_def /*? ' '.join(to_unfold) ?*/,
  /*- for a in tcbs.values() -*/
      case_tac "n = ''/*? a[0] ?*/'' \<and> i = /*? a[1] ?*/",
    /*- for b in tcbs.values() -*/
       case_tac "m = ''/*? b[0] ?*/'' \<and> j = /*? b[1] ?*/",
        clarsimp,
    /*- endfor -*/
       force,
  /*- endfor -*/
      force)
(** TPP: condense = False *)

(** TPP: condense = True *)
definition extra' :: cdl_heap
  where "extra' identifier \<equiv>
  /*- for obj in obj_space.spec.objs -*/
    /*- if obj.name is not none and isinstance(obj, (capdl.Frame, capdl.PageTable, capdl.PageDirectory)) -*/
    if identifier = /*? obj.name ?*/_id then Some /*? obj.name ?*/ else
    /*- endif -*/
  /*- endfor -*/
    None"
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma extra_only_pds_pts_frames:
  "case extra' x of None \<Rightarrow> True
                  | Some (PageDirectory _) \<Rightarrow> True
                  | Some (PageTable _) \<Rightarrow> True
                  | Some (Frame _) \<Rightarrow> True
                  | _ \<Rightarrow> False"
  by (simp add:extra'_def,
  /*- for obj in obj_space.spec.objs -*/
    /*- if obj.name is not none and isinstance(obj, (capdl.Frame, capdl.PageTable, capdl.PageDirectory)) -*/
      case_tac "x = /*? obj.name ?*/_id",
       simp add:/*? obj.name ?*/_def,
    /*- endif -*/
  /*- endfor -*/
      simp)
(** TPP: condense = False *)

lemma union_split: "\<lbrakk>A \<inter> C = {}; B \<inter> C = {}\<rbrakk> \<Longrightarrow> (A \<union> B) \<inter> C = {}"
by (simp add: inf_sup_distrib2)

interpretation Generator_CAMKES_CDL.cdl_translation ipc_buffer id_of
  apply unfold_locales
   apply (simp add:buffers_distinct')
  by (simp add:ids_distinct')

lemma cnode_objects_distinct:
  "dom (map_of (map (\<lambda>(x, y). (the (id_of x), y))
     (cnode_objs ArchSpec.assembly'))) \<inter> dom extra' = {}"
  by (subst dom_map_of_conv_image_fst,
      simp add:cnode_objs_def ArchSpec.assembly'_def ArchSpec.composition'_def
               id_of_def instance_names_def dom_def,
      code_simp)

(** TPP: condense = True *)
/*- set to_unfold = set(('tcb_objs_def', 'ArchSpec.assembly\'_def', 'ArchSpec.composition\'_def', 'id_of_def', 'instance_names_def', 'dom_def')) -*/
/*# During the proof of this lemma we'll need to unfold the definitions of all
 *# the component instances and their types.
 #*/
/*- for i in composition.instances -*/
  /*- do map(to_unfold.add, ('ArchSpec.%s_def' % i.name, 'ArchSpec.%s_def' % i.type.name)) -*/
/*- endfor -*/
lemma tcb_objects_distinct:
  "dom (map_of (map (\<lambda>(x, y). (the (id_of x), y))
     (tcb_objs ArchSpec.assembly'))) \<inter> dom extra' = {}"
  by (subst dom_map_of_conv_image_fst,
/*? '\n'.join(textwrap.wrap(' '.join(to_unfold), width=100, initial_indent='      simp add:', subsequent_indent=' ' * len('      simp add:'))) ?*/,
      code_simp)
(** TPP: condense = False *)

(** TPP: condense = True *)
/*- set to_unfold = set(('ArchSpec.assembly\'_def', 'ArchSpec.composition\'_def', 'ep_objs_def', 'ep_objs\'_def', 'id_of_def', 'dom_def')) -*/
/*# During the proof of this lemma we'll need to unfold the definitions of all
 *# the connections.
 #*/
/*- for c in composition.connections -*/
  /*- do to_unfold.add('ArchSpec.%s_def' % c.name) -*/
/*- endfor -*/
lemma ep_objects_distinct:
  "dom (map_of (map (\<lambda>(x, y). (the (id_of x), y))
     (ep_objs ArchSpec.assembly'))) \<inter> dom extra' = {}"
  apply (subst dom_map_of_conv_image_fst)
/*? '\n'.join(textwrap.wrap(' '.join(to_unfold), width=100, initial_indent='  apply (simp add:', subsequent_indent=' ' * len('  apply (simp add:'))) ?*/)
  (* XXX: Connection name mangling prevents the following proof for now. *)
  sorry
(** TPP: condense = False *)

lemma objects_distinct: "dom (cdl_objects (generate' ArchSpec.assembly')) \<inter> dom extra' = {}"
  apply (simp add:generate'_def obj_heap_def)
  apply (rule union_split)
   apply (simp add:cnode_objects_distinct)
  apply (rule union_split)
   apply (simp add:tcb_objects_distinct)
  by (simp add:ep_objects_distinct)

lemma extra_is_valid: "valid_extra (generate' ArchSpec.assembly') extra'"
  by (simp add:valid_extra_def extra_only_pds_pts_frames objects_distinct)

end
