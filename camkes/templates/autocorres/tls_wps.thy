/*- if 'autocorres/tls_wps.thy' not in included -*/
/*- do included.add('autocorres/tls_wps.thy') -*/

/*- include 'autocorres/inv.thy' -*/

/*- set threads = 1 + len(me.to_instance.type.provides + me.to_instance.type.uses + me.to_instance.type.emits + me.to_instance.type.consumes + me.to_instance.type.dataports) -*/

/*- for m in interface.methods -*/
  /*- for p in m.parameters -*/
    /*- set ptrs = [] -*/
    /*- for t in range(1, threads + 1) -*/
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
    /*- set fn = [None] -*/
    /*- if p.type.type in ['int8_t', 'uint8_t', 'char'] -*/
      /*- do fn.__setitem__(0, 'is_valid_w8') -*/
    /*- elif p.type.type in ['int16_t', 'uint16_t'] -*/
      /*- do fn.__setitem__(0, 'is_valid_w16') -*/
    /*- elif p.type.type in ['int32_t', 'uint32_t', 'int', 'unsigned int'] -*/
      /*- do fn.__setitem__(0, 'is_valid_w32') -*/
    /*- elif p.type.type in ['int64_t', 'uint64_t'] -*/
      /*- do fn.__setitem__(0, 'is_valid_w64') -*/
    /*- else -*/
      /*? raise(NotImplementedError()) ?*/
    /*- endif -*/
    /*- set subgoals = [] -*/
    /*- for t in range(1, threads + 1) -*/
      /*- do subgoals.append('subgoal_tac "%s s0 (Ptr (symbol_table \'\'%s_%s_%d\'\'))"' % (fn[0], m.name, p.name, t)) -*/
    /*- endfor -*/
  apply (/*? ',\n         '.join(subgoals) ?*/)
  /*? ' ' * len(subgoals) ?*/apply unat_arith
  /*? ' ' * (len(subgoals) - 1) ?*/apply (simp only:inv_def)+
  done
(** TPP: condense = False *)
  /*- endfor -*/
/*- endfor -*/

/*- endif -*/
