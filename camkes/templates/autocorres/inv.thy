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

/*- if 'autocorres/inv.thy' not in included -*/
/*- do included.add('autocorres/inv.thy') -*/

/*- if len(me.parent.to_ends) != 1 -*/
  /*? raise(TemplateError('connections without a single to end are not supported', me.parent)) ?*/
/*- endif -*/

(* Pointer to the IPC buffer. *)
definition
  ipc_buffer_ptr :: "lifted_globals \<Rightarrow> seL4_IPCBuffer__C ptr"
where
  "ipc_buffer_ptr s \<equiv> heap_seL4_IPCBuffer__C'ptr s (Ptr (scast seL4_GlobalsFrame))"

(* The IPC buffer itself. *)
definition
  ipc_buffer :: "lifted_globals \<Rightarrow> seL4_IPCBuffer__C"
where
  "ipc_buffer s \<equiv> heap_seL4_IPCBuffer__C s (ipc_buffer_ptr s)"

(* Predicate that the globals frame has not been affected by userspace. *)
definition
  globals_frame_intact :: "lifted_globals \<Rightarrow> bool"
where
  "globals_frame_intact s \<equiv>
    is_valid_seL4_IPCBuffer__C'ptr s (Ptr (scast seL4_GlobalsFrame))"

(* Predicate that the user still has a valid IPC buffer. *)
definition
  ipc_buffer_valid :: "lifted_globals \<Rightarrow> bool"
where
  "ipc_buffer_valid s \<equiv> is_valid_seL4_IPCBuffer__C s (ipc_buffer_ptr s)"

(* The pointer to the thread-local storage region. *)
definition
  tls_ptr :: "lifted_globals \<Rightarrow> camkes_tls_t_C ptr"
where
  "tls_ptr s \<equiv> Ptr (ptr_val (heap_seL4_IPCBuffer__C'ptr s
     (Ptr (scast seL4_GlobalsFrame))) && 0xFFFFF000)"

(* The thread-local storage region itself. *)
definition
  tls :: "lifted_globals \<Rightarrow> camkes_tls_t_C"
where
  "tls s \<equiv> heap_camkes_tls_t_C s (tls_ptr s)"

(* Predicate that the TLS region is valid. *)
definition
  tls_valid :: "lifted_globals \<Rightarrow> bool"
where
  "tls_valid s \<equiv> is_valid_camkes_tls_t_C s (tls_ptr s)"

/*# Note that this is calculated based on the to side, because only it uses TLS
 *# pointers.
 #*/
/*- set threads = 1 + len(me.parent.to_instance.type.provides + me.parent.to_instance.type.uses + me.parent.to_instance.type.emits + me.parent.to_instance.type.consumes + me.parent.to_instance.type.dataports) -*/
(* Number of threads in the system. *)
definition
  thread_count :: "32 word"
where
  "thread_count \<equiv> /*? threads ?*/"

definition
  thread_index :: "lifted_globals \<Rightarrow> 32 word"
where
  "thread_index s \<equiv> thread_index_C (tls s)"

definition
  thread_valid :: "lifted_globals \<Rightarrow> bool"
where
  "thread_valid s \<equiv> thread_index s \<in> {1..thread_count}"

/*- set invs = ['globals_frame_intact s', 'ipc_buffer_valid s', 'tls_valid s', 'thread_valid s'] -*/
/*- set distincts = [] -*/
/*- set inv_elims = {} -*/
/*- for m in interface.methods -*/
  /*- for p in m.parameters -*/
    /*- for t in six.moves.range(1, threads + 1) -*/
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
      /*- do invs.append('%s s (Ptr (symbol_table \'\'%s_%s_%d\'\'))' % (fn, m.name, p.name, t)) -*/
      /*- do inv_elims.__setitem__('inv_imp_%s_%s_%d_valid' % (m.name, p.name, t), 'inv s \<Longrightarrow> %s s (Ptr (symbol_table \'\'%s_%s_%d\'\'))' % (fn, m.name, p.name, t)) -*/
      /*- do distincts.append('symbol_table \'\'%s_%s_%d\'\'' % (m.name, p.name, t)) -*/
    /*- endfor -*/
  /*- endfor -*/
/*- endfor -*/
/*- if len(distincts) > 0 -*/
  /*- do invs.append('distinct [%s]' % ', '.join(distincts)) -*/
/*- endif -*/

(* Property that should always be true of the system. *)
definition
  inv :: "lifted_globals \<Rightarrow> bool"
where
  "inv s \<equiv> /*? ' \<and> '.join(invs) ?*/"

lemma inv_simps[simp]:
  "inv s \<Longrightarrow> globals_frame_intact s"
  "inv s \<Longrightarrow> ipc_buffer_valid s"
  "inv s \<Longrightarrow> tls_valid s"
  "inv s \<Longrightarrow> thread_valid s"
  by (simp add:inv_def)+

/*- for name, body in inv_elims.items() -*/
lemma /*? name ?*/:"/*? body ?*/"
  by (simp only:inv_def)+
/*- endfor -*/

/*- for m in interface.methods -*/
  /*- for p in m.parameters -*/
    /*- set ptrs = [] -*/
    /*- for t in six.moves.range(1, threads + 1) -*/
      /*- do ptrs.append('Ptr (symbol_table \'\'%s_%s_%d\'\')' % (m.name, p.name, t)) -*/
    /*- endfor -*/
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
(** TPP: condense = True *)
lemma inv_imp_/*? m.name ?*/_/*? p.name ?*/_valid1:
  "\<lbrakk>p \<in> {/*? ', '.join(ptrs) ?*/}; inv s\<rbrakk> \<Longrightarrow> /*? fn ?*/ s p"
  apply clarsimp
    /*- for t in six.moves.range(1, threads + 1) -*/
      /*- if loop.last -*/
  apply (simp add:inv_imp_/*? m.name ?*/_/*? p.name ?*/_/*? t ?*/_valid)
      /*- else -*/
  apply (erule disjE, simp add:inv_imp_/*? m.name ?*/_/*? p.name ?*/_/*? t ?*/_valid)
      /*- endif -*/
    /*- endfor -*/
  done
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma inv_imp_/*? m.name ?*/_/*? p.name ?*/_valid2:
  "\<lbrakk>p \<in> {/*? ', '.join(ptrs) ?*/}; inv s\<rbrakk> \<Longrightarrow> /*? fn ?*/ s (ptr_coerce p)"
  apply clarsimp
    /*- for t in six.moves.range(1, threads + 1) -*/
      /*- if loop.last -*/
  apply (simp add:inv_imp_/*? m.name ?*/_/*? p.name ?*/_/*? t ?*/_valid)
      /*- else -*/
  apply (erule disjE, simp add:inv_imp_/*? m.name ?*/_/*? p.name ?*/_/*? t ?*/_valid)
      /*- endif -*/
    /*- endfor -*/
  done
(** TPP: condense = False *)

lemmas inv_imp_/*? m.name ?*/_/*? p.name ?*/_valid = inv_imp_/*? m.name ?*/_/*? p.name ?*/_valid1 inv_imp_/*? m.name ?*/_/*? p.name ?*/_valid2
  /*- endfor -*/
/*- endfor -*/

/*- if len(distincts) > 0 -*/
lemma inv_imp_distincts:
  "inv s \<Longrightarrow> distinct [/*? ', '.join(distincts) ?*/]"
  by (simp only:inv_def)
/*- endif -*/

(* Definitions required to fully unfold the invariant. *)
lemmas inv_defs = inv_def globals_frame_intact_def ipc_buffer_valid_def
  ipc_buffer_ptr_def ipc_buffer_def tls_valid_def tls_ptr_def tls_def
  thread_valid_def thread_count_def thread_index_def

/*- endif -*/
