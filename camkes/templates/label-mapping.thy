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

/*# Forced garbage collection that we emit between proofs when debugging in
 *# order to keep an interactive Isabelle session manageable.
 #*/
/*- set gc = 'ML {* PolyML.fullGC () *}' if options.verbosity >= 2 else '' -*/

/*# Helpers for emitting different proof styles depending on whether debugging
 *# is enabled. This is useful for (a) speeding up completed proofs and (b)
 *# streamlining proof development.
 #*/
/*- set open_proof = 'sorry (*\n  apply (' if options.verbosity >= 2 else 'by (' -*/ /*# XXX: fix syntax highlighting: *) #*/
/*- set a = 'apply (' if options.verbosity >= 2 else '    ' -*/
/*- set A = ')' if options.verbosity >= 2 else ',' -*/
/*- set close_proof = ')\n  done *)' if options.verbosity >= 2 else ')' -*/

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
/*? '\n'.join(textwrap.wrap('  %sunfold %s%s' % (open_proof, ' '.join(to_unfold), A), width=100, subsequent_indent=' ' * len('  %sunfold ' % open_proof))) ?*/
  /*- for n in obj_space.spec.objs -*/
    /*- if n.name is not none -*/
  /*? a ?*/case_tac "n = ''/*? n.name ?*/''"/*? A ?*/
      /*- for m in obj_space.spec.objs -*/
        /*- if m.name is not none -*/
   /*? a ?*/case_tac "m = ''/*? m.name ?*/''"/*? A ?*/
        /*? a ?*/clarsimp/*? A ?*/
        /*- endif -*/
      /*- endfor -*/
   /*? a ?*/clarsimp/*? A ?*/
    /*- endif -*/
  /*- endfor -*/
  /*? a ?*/clarsimp/*? close_proof ?*/

/*? gc ?*/
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
  /*? open_proof ?*/unfold ipc_buffer_def /*? ' '.join(to_unfold) ?*//*? A ?*/
  /*- for v1 in tcbs.values() -*/
  /*? a ?*/case_tac "n = ''/*? v1[0] ?*/'' \<and> i = /*? v1[1] ?*/"/*? A ?*/
    /*- for v2 in tcbs.values() -*/
   /*? a ?*/case_tac "m = ''/*? v2[0] ?*/'' \<and> j = /*? v2[1] ?*/"/*? A ?*/
    /*? a ?*/clarsimp/*? A ?*/
    /*- endfor -*/
   /*? a ?*/force/*? A ?*/
  /*- endfor -*/
  /*? a ?*/force/*? close_proof ?*/

/*? gc ?*/
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
  /*? open_proof ?*/unfold extra'_def/*? A ?*/
  /*- for obj in obj_space.spec.objs -*/
    /*- if obj.name is not none and isinstance(obj, (capdl.Frame, capdl.PageTable, capdl.PageDirectory)) -*/
  /*? a ?*/case_tac "x = /*? obj.name ?*/_id"/*? A ?*/
   /*? a ?*/simp add:/*? obj.name ?*/_def/*? A ?*/
    /*- endif -*/
  /*- endfor -*/
  /*? a ?*/simp/*? close_proof ?*/

/*? gc ?*/
(** TPP: condense = False *)

lemma union_split: "\<lbrakk>A \<inter> C = {}; B \<inter> C = {}\<rbrakk> \<Longrightarrow> (A \<union> B) \<inter> C = {}"
  by (simp add: inf_sup_distrib2)

(** TPP: condense = True *)
interpretation Generator_CAMKES_CDL.cdl_translation ipc_buffer id_of
  /*? open_proof ?*/unfold_locales/*? A ?*/
   /*? a ?*/simp add:buffers_distinct'/*? A ?*/
  /*? a ?*/simp add:ids_distinct'/*? close_proof ?*/

/*? gc ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma cnode_objects_distinct:
  "dom (map_of (map (\<lambda>(x, y). (the (id_of x), y))
     (cnode_objs ArchSpec.assembly'))) \<inter> dom extra' = {}"
  /*? open_proof ?*/subst dom_map_of_conv_image_fst/*? A ?*/
  /*? a ?*/simp add:cnode_objs_def ArchSpec.assembly'_def ArchSpec.composition'_def
               id_of_def instance_names_def dom_def/*? A ?*/
  /*? a ?*/code_simp/*? close_proof ?*/

/*? gc ?*/
(** TPP: condense = False *)

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
  /*? open_proof ?*/subst dom_map_of_conv_image_fst/*? A ?*/
/*? '\n'.join(textwrap.wrap(' '.join(to_unfold), width=100, initial_indent='  %ssimp add:' % a, subsequent_indent=' ' * len('  %ssimp add:' % s))) ?*//*? A ?*/
  /*? a ?*/code_simp/*? close_proof ?*/
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
  /*? open_proof ?*/simp add:generate'_def obj_heap_def/*? A ?*/
  /*? a ?*/rule union_split/*? A ?*/
   /*? a ?*/simp add:cnode_objects_distinct/*? A ?*/
  /*? a ?*/rule union_split/*? A ?*/
   /*? a ?*/simp add:tcb_objects_distinct/*? A ?*/
  /*? a ?*/simp add:ep_objects_distinct/*? close_proof ?*/

lemma extra_is_valid: "valid_extra (generate' ArchSpec.assembly') extra'"
  by (simp add:valid_extra_def extra_only_pds_pts_frames objects_distinct)

definition irqs :: irqs
  where "irqs \<equiv> \<lparr>
    irqs_map = CapDLSpec.irqs,
    irqs_objects = CapDLSpec.empty_irq_objects\<rparr>"

lemma dom_expand: "dom (\<lambda>x. if P x then Some y else None) = {x. P x}"
  using if_option_Some by fastforce

lemma range_translate: "(range f = range g) = ((\<forall>x. \<exists>y. f x = g y) \<and> (\<forall>x. \<exists>y. f y = g x))"
  /*? open_proof ?*/rule iffI/*? A ?*/
   /*? a ?*/rule conjI/*? A ?*/
    /*? a ?*/clarsimp/*? A ?*/
    /*? a ?*/blast/*? A ?*/
   /*? a ?*/clarsimp/*? A ?*/
   /*? a ?*/metis helper8 range_eqI/*? A ?*/
  /*? a ?*/clarsimp/*? A ?*/
  /*? a ?*/subst set_eq_subset/*? A ?*/
  /*? a ?*/rule conjI/*? A ?*/
   /*? a ?*/clarsimp/*? A ?*/
   /*? a ?*/rename_tac arg/*? A ?*/
   /*? a ?*/erule_tac x=arg and P="\<lambda>x. (\<exists>y. f x = g y)" in allE/*? A ?*/
   /*? a ?*/clarsimp/*? A ?*/
  /*? a ?*/clarsimp/*? A ?*/
  /*? a ?*/rename_tac arg/*? A ?*/
  /*? a ?*/erule_tac x=arg and P="\<lambda>x. (\<exists>y. f y = g x)" in allE/*? A ?*/
  /*? a ?*/clarsimp/*? A ?*/
  /*? a ?*/metis range_eqI/*? close_proof ?*/

(** TPP: condense = True *)
/*# The IRQs are represented as empty CNodes, inferred by the CapDL translator
 *# to directly follow the explicit objects. We can thus calculate their object
 *# IDs by counting the objects we have explicitly. We need to create
 *# definitions like this and the lunacy that follows to deal with scalability
 *# problems in Isabelle stemming from unfolding the CapDLSpec.irqs map.
 #*/
/*- set irq_ids = list(range(len(obj_space.spec.objs), len(obj_space.spec.objs) + 256)) -*/
definition range_irqs :: "cdl_object_id set"
/*? '\n'.join(textwrap.wrap('  where "range_irqs \\<equiv> {%s}"' % ', '.join(map(str, irq_ids)), width=100, subsequent_indent=' ' * len('  where "range_irqs = {'))) ?*/ /*# XXX: fix syntax highlighting: " #*/
(** TPP: condense = False *)

(** TPP: condense = True *)
/*- for irq, id in enumerate(irq_ids) -*/
lemma irq_/*? irq ?*/: "CapDLSpec.irqs /*? irq ?*/ = /*? id ?*/"
  /*? open_proof ?*/simp add:CapDLSpec.irqs_def/*? close_proof ?*/
/*- endfor -*/
(** TPP: condense = False *)

lemma set_enum_def:
/*? '\n'.join(textwrap.wrap('  "((set enum)::word8 set) = {%s}"' % ', '.join(map(str, range(256))), width=100, subsequent_indent=' ' * len('  "((set enum)::word8 set) = {'))) ?*/ /*# XXX: fix syntax highlighting: " #*/
  /*? open_proof ?*/eval/*? close_proof ?*/

(** TPP: condense = True *)
lemma word8_exhaust:
  fixes x :: word8
/*? '\n'.join(textwrap.wrap('  shows "\\<lbrakk>%s\\<rbrakk> \\<Longrightarrow> P"' % '; '.join(map(lambda('x: \'x \\\\<noteq> %d\' % x'), range(256))), width=100, subsequent_indent=' ' * len('  shows "['))) ?*/ /*# XXX: fix syntax highlighting: " #*/
  apply (subgoal_tac "x \<in> set enum")
   prefer 2
   apply simp
  apply (subst (asm) set_enum_def)
  by simp
(** TPP: condense = False *)

(** TPP: condense = True *)
(* XXX: This proof reads like a verbose suicide note and requires around 10GB of RAM. That seems a bit much. *)
lemma range_irqs_eq: "range CapDLSpec.irqs = range_irqs"
  /*? open_proof ?*/subst set_eq_subset/*? A ?*/
  /*? a ?*/rule conjI/*? A ?*/
   /*? a ?*/subst subset_eq/*? A ?*/
   /*? a ?*/simp add:range_irqs_def/*? A ?*/
   /*# At this point, we need to tread very lightly because invoking the
    *# simplifier to discharge even obvious contradictions is quite expensive.
    #*/
   /*? a ?*/rule allI/*? A ?*/
   /*- for i in range(256) -*/
   /*? a ?*/case_tac "x = /*? i ?*/"/*? A ?*/
    /*- for j in range(i) -*/
    /*? a ?*/rule disjI2/*? A ?*/
    /*- endfor -*/
    /*- if not loop.last -*/
    /*? a ?*/rule disjI1/*? A ?*/
    /*- endif -*/
    /*? a ?*/simp/*? A ?*/ /*# assumptions should be sufficiently minimal now #*/
    /*? a ?*/subst irq_/*? i ?*//*? A ?*/
    /*? a ?*/rule refl/*? A ?*/
   /*- endfor -*/
   /*? a ?*/rule FalseE/*? A ?*/ (* ditch expensive conclusion *)
   /*? a ?*/(rule_tac x=x in word8_exhaust; simp_all)/*? A ?*/
  /*? a ?*/clarsimp simp:range_irqs_def/*? A ?*/
  /*# Again, too expensive to use the simplifier from here on. #*/
  /*- for i in range(256) -*/
    /*- if not loop.last -*/
  /*? a ?*/rule conjI/*? A ?*/
   /*? a ?*/rule_tac x=/*? i ?*/ in range_eqI/*? A ?*/
   /*? a ?*/subst irq_/*? i ?*//*? A ?*/
   /*? a ?*/rule refl/*? A ?*/
    /*- else -*/
  /*? a ?*/rule_tac x=/*? i ?*/ in range_eqI/*? A ?*/    
  /*? a ?*/subst irq_/*? i ?*//*? A ?*/
  /*? a ?*/rule refl/*? close_proof ?*/
    /*- endif -*/
  /*- endfor -*/
(** TPP: condense = False *)

lemma le_step:
  fixes x :: cdl_object_id
  shows "\<lbrakk>x \<le>  y; x \<noteq> y; y < 2 ^ 32 - 1\<rbrakk> \<Longrightarrow> x \<le> y - 1"
  /*? open_proof ?*/subst (asm) word_le_less_eq/*? A ?*/
  /*? a ?*/clarsimp/*? A ?*/
  /*? a ?*/simp add: minus_one_helper3/*? close_proof ?*/

lemma upper_trivial:
  fixes x :: cdl_object_id
  shows "x \<noteq> 2 ^ 32 - 1 \<Longrightarrow> x < 2 ^ 32 - 1"
  /*? open_proof ?*/cut_tac n=x and 'a=32 in max_word_max/*? A ?*/
  /*? a ?*/clarsimp simp:max_word_def/*? A ?*/
  /*? a ?*/simp add: less_le/*? close_proof ?*/

(** TPP: condense = True *)
lemma range_irqs_exhaust:
  fixes x :: cdl_object_id
/*? '\n'.join(textwrap.wrap('  shows "\\<lbrakk>%d \\<le> x; x \\<le> %d; %s\\<rbrakk> \\<Longrightarrow> P"' % (min(irq_ids), max(irq_ids), '; '.join(map(lambda('x: \'x \\\\<noteq> %d\' % x'), irq_ids))), width=100, subsequent_indent=' ' * len('  shows "['))) ?*/ /*# XXX: fix syntax highlighting: " #*/
  (* warning: takes a LONG time *)
  /*? open_proof ?*/(drule le_step, assumption, rule upper_trivial, simp+)+/*? close_proof ?*/
(** TPP: condense = False *)

lemma constraint_expand:
  fixes x :: cdl_object_id
  shows "x \<in> {y. lower \<le> y \<and> y \<le> upper} = (lower \<le> x \<and> x \<le> upper)"
  by simp

(** TPP: condense = True *)
lemma range_irqs_def2: "range_irqs = {x. /*? min(irq_ids) ?*/ \<le> x \<and> x \<le> /*? max(irq_ids) ?*/}"
  /*? open_proof ?*/subst set_eq_subset/*? A ?*/
  /*? a ?*/rule conjI/*? A ?*/
   /*? a ?*/simp add:range_irqs_def/*? A ?*/
  /*? a ?*/subst subset_iff/*? A ?*/
  /*? a ?*/rule allI/*? A ?*/
  /*? a ?*/rename_tac obj_id/*? A ?*/
  /*? a ?*/rule impI/*? A ?*/
  /*? a ?*/subst (asm) constraint_expand/*? A ?*/
  /*? a ?*/clarsimp simp:range_irqs_def/*? A ?*/
  /*? a ?*/rule ccontr/*? A ?*/
  /*? a ?*/(rule_tac x=obj_id in range_irqs_exhaust; assumption)/*? close_proof ?*/

/*? gc ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma irqs_dom_distinct_cnodes:
/*- set to_unfold = set(('cnode_objs_def', 'instance_names_def', 'ArchSpec.assembly\'_def', 'ArchSpec.composition\'_def', 'id_of_def', 'CapDLSpec.empty_irq_objects_def')) -*/
/*- for i in composition.instances -*/
  /*- do to_unfold.add('CapDLSpec.cnode_%s_id_def' % i.name) -*/
/*- endfor -*/
  "dom (map_of (map (\<lambda>(n, y). (the (id_of n), y)) (cnode_objs assembly')))
     \<inter> dom empty_irq_objects = {}"
/*? '\n'.join(textwrap.wrap('  %ssimp add:%s%s' % (open_proof, ' '.join(to_unfold), A), width=100, subsequent_indent=' ' * len('  %ssimp add:' % open_proof))) ?*/
  /*? a ?*/(subst dom_expand)+/*? A ?*/
  /*? a ?*/clarsimp, unat_arith?/*? close_proof ?*/

/*? gc ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma irqs_dom_distinct_tcbs:
/*- set to_unfold = set(('tcb_objs_def', 'ArchSpec.assembly\'_def', 'ArchSpec.composition\'_def', 'ArchSpec.composition\'_def', 'id_of_def', 'CapDLSpec.empty_irq_objects_def')) -*/
/*- for i in composition.instances -*/
  /*- do to_unfold.add('CapDLSpec.%s_tcb__control_id_def' % i.name) -*/
  /*- do to_unfold.add('ArchSpec.%s_def' % i.name) -*/
  /*- do to_unfold.add('ArchSpec.%s_def' % i.type.name) -*/
  /*- for inf in i.type.provides + i.type.uses + i.type.emits + i.type.consumes + i.type.dataports -*/
    /*- do to_unfold.add('CapDLSpec.%s_tcb_%s_id_def' % (i.name, inf.name)) -*/
  /*- endfor -*/
/*- endfor -*/
  "dom (map_of (map (\<lambda>(n, y). (the (id_of n), y)) (tcb_objs assembly')))
     \<inter> dom empty_irq_objects = {}"
/*? '\n'.join(textwrap.wrap('  %ssimp add:%s%s' % (open_proof, ' '.join(to_unfold), A), width=100, subsequent_indent=' ' * len('  %ssimp add:' % open_proof))) ?*/
  /*? a ?*/(subst dom_expand)+/*? A ?*/
  /*? a ?*/clarsimp, unat_arith?/*? close_proof ?*/

/*? gc ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma irqs_dom_distinct_eps:
  "dom (map_of (map (\<lambda>(n, y). (the (id_of n), y)) (ep_objs assembly')))
     \<inter> dom empty_irq_objects = {}"
  sorry (* XXX: we can't prove this because of connection name mangling currently *)

/*? gc ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma irqs_dom_distinct:
  "dom (cdl_objects (generate' assembly')) \<inter> {x. /*? min(irq_ids) ?*/ \<le> x \<and> x \<le> /*? max(irq_ids) ?*/} = {}"
  /*? open_proof ?*/simp add:generate'_def obj_heap_def/*? A ?*/
  /*? a ?*/rule union_split/*? A ?*/
   /*? a ?*/cut_tac irqs_dom_distinct_cnodes[unfolded empty_irq_objects_def]/*? A ?*/
   /*? a ?*/subst (asm) dom_expand/*? A ?*/
   /*? a ?*/assumption/*? A ?*/
  /*? a ?*/rule union_split/*? A ?*/
   /*? a ?*/cut_tac irqs_dom_distinct_tcbs[unfolded empty_irq_objects_def]/*? A ?*/
   /*? a ?*/subst (asm) dom_expand/*? A ?*/
   /*? a ?*/assumption/*? A ?*/
  /*? a ?*/cut_tac irqs_dom_distinct_eps[unfolded empty_irq_objects_def]/*? A ?*/
  /*? a ?*/subst (asm) dom_expand/*? A ?*/
  /*? a ?*/assumption/*? close_proof ?*/

/*? gc ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma irqs_dom_distinct_extra: "dom extra' \<inter> {x. /*? min(irq_ids) ?*/ \<le> x \<and> x \<le> /*? max(irq_ids) ?*/} = {}"
  /*? open_proof ?*/rule disjointI/*? A ?*/
  /*? a ?*/rename_tac x y/*? A ?*/
  /*? a ?*/drule domD/*? A ?*/
  /*- for obj in obj_space.spec.objs -*/
    /*- if obj.name is not none and isinstance(obj, (capdl.Frame, capdl.PageTable, capdl.PageDirectory)) -*/
  /*? a ?*/case_tac "x = /*? obj.name ?*/_id"/*? A ?*/
   /*? a ?*/simp add:extra'_def /*? obj.name ?*/_id_def/*? A ?*/
   /*? a ?*/fastforce/*? A ?*/
    /*- endif -*/
  /*- endfor -*/
  /*? a ?*/simp add:extra'_def/*? close_proof ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma ran_expand: "\<exists>x. P x \<Longrightarrow> ran (\<lambda>x. if P x then Some y else None) = {y}"
  /*? open_proof ?*/rule subset_antisym/*? A ?*/
   /*? a ?*/(clarsimp simp:ran_def)+/*? close_proof ?*/

/*? gc ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma irqs_is_valid: "valid_irqs (generate' ArchSpec.assembly') extra' irqs"
  /*? open_proof ?*/simp add:valid_irqs_def irqs_def CapDLSpec.empty_irq_objects_def/*? A ?*/
  /*? a ?*/(subst dom_expand)+/*? A ?*/
  /*? a ?*/rule conjI/*? A ?*/
   /*? a ?*/subst range_irqs_eq/*? A ?*/
   /*? a ?*/subst range_irqs_def2/*? A ?*/
   /*? a ?*/rule refl/*? A ?*/
  /*? a ?*/rule conjI/*? A ?*/
   /*? a ?*/simp add:irqs_dom_distinct/*? A ?*/
  /*? a ?*/rule conjI/*? A ?*/
   /*? a ?*/simp add:irqs_dom_distinct_extra/*? A ?*/
  /*? a ?*/simp/*? A ?*/
  /*? a ?*/subst ran_expand/*? A ?*/
   /*? a ?*/rule exI, force/*? A ?*/
  /*? a ?*/simp add:CapDLSpec.empty_irq_node_def/*? close_proof ?*/

/*? gc ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma spec_generation_correct: "generate ArchSpec.assembly' extra' irqs = Some CapDLSpec.state"
  apply (simp add:generate_def extra_is_valid merge_objs_def merge_cdl_def CapDLSpec.state_def
                  irqs_is_valid)
  apply (rule cdl_state.equality, simp_all)
        apply (simp add:generate'_def)
       defer
      apply (simp add:generate'_def CapDLSpec.cdt_def)
     apply (simp add:generate'_def)
    apply (simp add:irqs_def)
   apply (simp add:generate'_def CapDLSpec.asid_table_def)
  apply (simp add:generate'_def)
  oops

/*? gc ?*/
(** TPP: condense = False *)

end
