/*#
 *# Copyright 2017, Data61
 *# Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 *# ABN 41 687 119 230.
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(DATA61_BSD)
 #*/

/*- if 'autocorres/tls_wps.thy' not in included -*/
/*- do included.add('autocorres/tls_wps.thy') -*/

/*- if len(me.parent.to_ends) != 1 -*/
  /*? raise(TemplateError('connections without a single to end are not supported', me.parent)) ?*/
/*- endif -*/

/*- include 'autocorres/inv.thy' -*/

/*- set threads = 1 + len(me.parent.to_instance.type.provides + me.parent.to_instance.type.uses + me.parent.to_instance.type.emits + me.parent.to_instance.type.consumes + me.parent.to_instance.type.dataports) -*/

/*- for m in interface.methods -*/
  /*- for p in m.parameters -*/
    /*- set ptrs = [] -*/
    /*- for t in six.moves.range(1, threads + 1) -*/
      /*- do ptrs.append('Ptr (symbol_table \'\'%s_%s_%d\'\')' % (m.name, p.name, t)) -*/
    /*- endfor -*/
(** TPP: condense = True *)
lemma get_/*? m.name ?*/_/*? p.name ?*/_wp[THEN validNF_make_schematic_post, simplified]:
  "\<forall>s0. \<lbrace>\<lambda>s. s = s0 \<and> inv s\<rbrace>
          get_/*? m.name ?*/_/*? p.name ?*/'
        \<lbrace>\<lambda>r s. s = s0 \<and> r \<in> {/*? ', '.join(ptrs) ?*/} \<and> inv s\<rbrace>!"
  apply (rule allI)
  unfolding get_/*? m.name ?*/_/*? p.name ?*/'_def apply (wp camkes_get_tls_wp)
  apply clarsimp
  apply (frule inv_simps(3), unfold tls_valid_def, simp)
  apply (frule inv_simps(4),
         unfold thread_valid_def thread_index_def thread_count_def tls_def)
  /*# ffs... #*/
    /*- if p.type in ['int8_t', 'uint8_t', 'char'] -*/
      /*- set fn = 'is_valid_w8' -*/
    /*- elif p.type in ['int16_t', 'uint16_t'] -*/
      /*- set fn = 'is_valid_w16' -*/
    /*- elif p.type in ['int32_t', 'uint32_t', 'int', 'unsigned int'] -*/
      /*- set fn = 'is_valid_w32' -*/
    /*- elif p.type in ['int64_t', 'uint64_t'] -*/
      /*- set fn = 'is_valid_w64' -*/
    /*- else -*/
      /*? raise(TemplateError('unsupported')) ?*/
    /*- endif -*/
    /*- set subgoals = [] -*/
    /*- for t in six.moves.range(1, threads + 1) -*/
      /*- do subgoals.append('subgoal_tac "%s s0 (Ptr (symbol_table \'\'%s_%s_%d\'\'))"' % (fn, m.name, p.name, t)) -*/
    /*- endfor -*/
  apply (/*? ',\n         '.join(subgoals) ?*/)
  /*? ' ' * len(subgoals) ?*/apply unat_arith
  /*? ' ' * (len(subgoals) - 1) ?*/apply (simp only:inv_def)+
  done
(** TPP: condense = False *)
  /*- endfor -*/
/*- endfor -*/

/*- endif -*/
