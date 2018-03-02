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

/*- if len(me.parent.to_ends) != 1 -*/
  /*? raise(TemplateError('connections with multiple to ends are not supported', me.parent)) ?*/
/*- endif -*/

/*- set thy = me.interface.name -*/
header {* RPC Receive *}
(*<*)
theory "/*? thy ?*/" imports
  "~~/../l4v/tools/c-parser/CTranslation"
  "~~/../l4v/tools/autocorres/AutoCorres"
  "~~/../l4v/tools/autocorres/NonDetMonadEx"
begin

(* THIS THEORY IS GENERATED. DO NOT EDIT.
 * It is expected to be hosted in l4v/camkes/glue-proofs.
 *)

(* ucast is type-polymorphic, but often appears in a visually indistinguishable form in proofs.
 * These abbreviations help you identify which type signature you're looking at. These
 * abbreviations need to exist outside the locale in order to be used in output.
 *)
abbreviation "ucast_32_to_32 \<equiv> ucast :: word32 \<Rightarrow> word32"
abbreviation "ucast_s32_to_32 \<equiv> ucast :: sword32 \<Rightarrow> word32"
abbreviation "ucast_32_to_s32 \<equiv> ucast :: word32 \<Rightarrow> sword32"
abbreviation "ucast_s32_to_s32 \<equiv> ucast :: sword32 \<Rightarrow> sword32"

(* As above for scast. *)
abbreviation "scast_32_to_32 \<equiv>   scast :: word32 \<Rightarrow> word32"
abbreviation "scast_s32_to_32 \<equiv>  scast :: sword32 \<Rightarrow> word32"
abbreviation "scast_32_to_s32 \<equiv>  scast :: word32 \<Rightarrow> sword32"
abbreviation "scast_s32_to_s32 \<equiv> scast :: sword32 \<Rightarrow> sword32"

declare [[allow_underscore_idents=true]]

install_C_file "/*? thy ?*/_seL4RPCSimple_pruned.c_pp"

(* Use non-determinism instead of the standard option monad type stregthening and do not heap
 * abstract seL4_SetMR.
 *)
autocorres [ts_rules = nondet, no_heap_abs = seL4_SetMR] "/*? thy ?*/_seL4RPCSimple_pruned.c_pp"

context "/*? thy ?*/_seL4RPCSimple_pruned" begin

definition
  seL4_SetMR_lifted' :: "int \<Rightarrow> word32 \<Rightarrow> lifted_globals \<Rightarrow> (unit \<times> lifted_globals) set \<times> bool"
where
  "seL4_SetMR_lifted' i val \<equiv>
   do
     ret' \<leftarrow> seL4_GetIPCBuffer';
     guard (\<lambda>s. i < uint seL4_MsgMaxLength);
     guard (\<lambda>s. 0 \<le> i);
     modify (\<lambda>s. s \<lparr>heap_seL4_IPCBuffer__C := (heap_seL4_IPCBuffer__C s)(ret' :=
        msg_C_update  (
            \<lambda>a. Arrays.update a (nat i) val) (heap_seL4_IPCBuffer__C s ret')
          )  \<rparr>)
  od"

definition
  globals_frame_intact :: "lifted_globals \<Rightarrow> bool"
where
  "globals_frame_intact s \<equiv> is_valid_seL4_IPCBuffer__C'ptr s (Ptr (scast seL4_GlobalsFrame))"

definition
  ipc_buffer_valid :: "lifted_globals \<Rightarrow> bool"
where
  "ipc_buffer_valid s \<equiv> is_valid_seL4_IPCBuffer__C s (heap_seL4_IPCBuffer__C'ptr s (Ptr (scast seL4_GlobalsFrame)))"

(* Various definitions used in assumptions on the TLS region. *)
definition
  tls_ptr :: "lifted_globals \<Rightarrow> camkes_tls_t_C ptr"
where
  "tls_ptr s \<equiv> Ptr (ptr_val (heap_seL4_IPCBuffer__C'ptr s
     (Ptr (scast_s32_to_32 seL4_GlobalsFrame))) && 0xFFFFF000)"
definition
  tls :: "lifted_globals \<Rightarrow> camkes_tls_t_C"
where
  "tls s \<equiv> heap_camkes_tls_t_C s (tls_ptr s)"
definition
  tls_valid :: "lifted_globals \<Rightarrow> bool"
where
  "tls_valid s \<equiv> is_valid_camkes_tls_t_C s (tls_ptr s)"

/*- set threads = 1 + len(me.instance.type.provides + me.instance.type.uses + me.instance.type.emits + me.instance.type.consumes + me.instance.type.dataports) -*/
definition
  thread_count :: word32
where
  "thread_count \<equiv> /*? threads ?*/"

definition
  setMR :: "lifted_globals \<Rightarrow> nat \<Rightarrow> word32 \<Rightarrow> lifted_globals"
where
  "setMR s i v \<equiv>
      s\<lparr>heap_seL4_IPCBuffer__C := (heap_seL4_IPCBuffer__C s)
        (heap_seL4_IPCBuffer__C'ptr s (Ptr (scast seL4_GlobalsFrame)) :=
          msg_C_update (\<lambda>a. Arrays.update a i v)
            (heap_seL4_IPCBuffer__C s (heap_seL4_IPCBuffer__C'ptr s
              (Ptr (scast seL4_GlobalsFrame)))))\<rparr>"

definition
  setMRs :: "lifted_globals \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow>
             word32 \<Rightarrow> word32 \<Rightarrow> lifted_globals"
where
  "setMRs s mr0 mr1 mr2 mr3 \<equiv>
    setMR (setMR (setMR (setMR s 0 mr0) 1 mr1) 2 mr2) 3 mr3"

(* Various simp rules for dealing with irrelevant updates to the state. *)
/*- set x = isabelle_symbol('x') -*/
/*- set s = isabelle_symbol('s') -*/
/*- set simps_emitted = set() -*/
/*- for m in me.interface.type.methods -*/
  /*- for p in m.parameters -*/
    /*- set w = macros.sizeof(options.architecture, p) * 8 -*/
    /*- if w not in simps_emitted -*/
lemma [simp]:"globals_frame_intact (heap_w/*? w ?*/_update /*? x ?*/ /*? s ?*/) = globals_frame_intact /*? s ?*/"
  by (simp add:globals_frame_intact_def)
lemma [simp]:"ipc_buffer_valid (heap_w/*? w ?*/_update /*? x ?*/ /*? s ?*/) = ipc_buffer_valid /*? s ?*/"
  by (simp add:ipc_buffer_valid_def)
lemma [simp]:"tls_valid (heap_w/*? w ?*/_update /*? x ?*/ /*? s ?*/) = tls_valid /*? s ?*/"
  by (simp add:tls_valid_def tls_ptr_def)
lemma [simp]:"thread_index_C (tls (heap_w/*? w ?*/_update /*? x ?*/ /*? s ?*/)) = thread_index_C (tls /*? s ?*/)"
  by (simp add:tls_def tls_ptr_def)
      /*- do simps_emitted.add(w) -*/
    /*- endif -*/
  /*- endfor -*/
/*- endfor -*/
/*- set i = isabelle_symbol('i') -*/
lemma [simp]:"/*? i ?*/ \<ge> 0 \<and> /*? i ?*/ < unat seL4_MsgMaxLength \<Longrightarrow>
    globals_frame_intact (setMR /*? s ?*/ /*? i ?*/ /*? x ?*/) = globals_frame_intact /*? s ?*/"
  by (simp add:setMR_def globals_frame_intact_def seL4_MsgMaxLength_def)
lemma [simp]:"/*? i ?*/ \<ge> 0 \<and> /*? i ?*/ < unat seL4_MsgMaxLength \<Longrightarrow>
    ipc_buffer_valid (setMR /*? s ?*/ /*? i ?*/ /*? x ?*/) = ipc_buffer_valid /*? s ?*/"
  by (simp add:setMR_def ipc_buffer_valid_def seL4_MsgMaxLength_def)
lemma [simp]:"/*? i ?*/ \<ge> 0 \<and> /*? i ?*/ < unat seL4_MsgMaxLength \<Longrightarrow>
    tls_valid (setMR /*? s ?*/ /*? i ?*/ /*? x ?*/) = tls_valid /*? s ?*/"
  by (simp add:setMR_def tls_valid_def tls_ptr_def seL4_MsgMaxLength_def)
lemma [simp]:"/*? i ?*/ \<ge> 0 \<and> /*? i ?*/ < unat seL4_MsgMaxLength \<Longrightarrow>
    thread_index_C (tls (setMR /*? s ?*/ /*? i ?*/ /*? x ?*/)) = thread_index_C (tls /*? s ?*/)"
  by (simp add:setMR_def tls_def tls_ptr_def seL4_MsgMaxLength_def)

/*- for m in me.interface.type.methods -*/
  /*- for p in m.parameters -*/
    /*- for t in six.moves.range(threads) -*/
lemma [simp]:"/*? i ?*/ \<ge> 0 \<and> /*? i ?*/ < unat seL4_MsgMaxLength \<Longrightarrow>
    is_valid_w/*? macros.sizeof(options.architecture, p) * 8 ?*/ (setMR /*? s ?*/ /*? i ?*/ /*? x ?*/) (Ptr (symbol_table ''/*? m.name ?*/_/*? p.name ?*/_/*? t + 1 ?*/'')) = is_valid_w/*? macros.sizeof(options.architecture, p) * 8 ?*/ /*? s ?*/ (Ptr (symbol_table ''/*? m.name ?*/_/*? p.name ?*/_/*? t + 1 ?*/''))"
  by (simp add:setMR_def seL4_MsgMaxLength_def)
    /*- endfor -*/
  /*- endfor -*/
/*- endfor -*/

(* Invariant to be preserved by user code and glue code. *)
/*- set state = isabelle_symbol('s') -*/
definition
  inv :: "lifted_globals \<Rightarrow> bool"
where
  "inv /*? state ?*/ \<equiv>
    globals_frame_intact /*? state ?*/ \<and>
    ipc_buffer_valid /*? state ?*/ \<and>
    tls_valid /*? state ?*/ \<and>
    thread_index_C (tls /*? state ?*/) \<in> {1..thread_count}
    /*- for m in me.interface.type.methods -*/
      /*- for p in m.parameters -*/
        /*- for t in six.moves.range(threads) -*/
          \<and> is_valid_w/*? macros.sizeof(options.architecture, p) * 8 ?*/ /*? state ?*/ (Ptr (symbol_table ''/*? m.name ?*/_/*? p.name ?*/_/*? t + 1 ?*/''))
        /*- endfor -*/
      /*- endfor -*/
    /*- endfor -*/
  "

end

locale /*? thy ?*/_seL4RPCSimple_glue = /*? thy ?*/_seL4RPCSimple_pruned +
  assumes seL4_SetMR_axiom: "exec_concrete lift_global_heap (seL4_SetMR' i val) = seL4_SetMR_lifted' i val"
(** TPP: condense = True *)
/*- for m in me.interface.type.methods -*/
  /*- set name = '%s_%s' % (me.interface.name, m.name) -*/
  fixes /*? name ?*/_spec
  assumes /*? name ?*/_spec_rel:
  /*- set state0 = isabelle_symbol('s0') -*/
  /*- set state = isabelle_symbol('s') -*/
  /*- set statep = isabelle_symbol('s') -*/
  "\<forall>/*? state0 ?*/. \<lbrace>\<lambda>/*? state ?*/. /*? state ?*/ = /*? state0 ?*/\<rbrace> /*? name ?*/'
  /*- set params = [] -*/
  /*- for p in m.parameters -*/
    /*- set param = isabelle_symbol(p.name) -*/
    /*? param ?*/
    /*- do params.append(param) -*/
  /*- endfor -*/
  /*- set ret = isabelle_symbol('r') -*/
  /*- set prop = isabelle_symbol('P') -*/
  \<lbrace>\<lambda>/*? ret ?*/ /*? statep ?*/. /*? name ?*/_spec /*? state0 ?*/ /*? statep ?*/ /*? ' '.join(params) ?*/ /*? ret ?*/\<rbrace>!"
  assumes /*? name ?*/_inv:
    "\<lbrakk>/*? name ?*/_spec /*? state ?*/ /*? statep ?*/ /*? ' '.join(params) ?*/ /*? ret ?*/; inv /*? state ?*/\<rbrakk> \<Longrightarrow> inv /*? statep ?*/"
/*- endfor -*/
(** TPP: condense = False *)
begin

/*- for m in me.interface.type.methods -*/
lemmas /*? me.interface.name ?*/_/*? m.name ?*/_wp[wp_unsafe] =
  /*? me.interface.name ?*/_/*? m.name ?*/_spec_rel[THEN validNF_make_schematic_post, simplified]
/*- endfor -*/

lemma abort_wp[wp]:
  "\<lbrace>\<lambda>_. False\<rbrace> abort' \<lbrace>P\<rbrace>!"
  by (rule validNF_false_pre)

lemma seL4_GetIPCBuffer_wp':
  "\<forall>s'. \<lbrace>\<lambda>s. globals_frame_intact s \<and>
             s = s'\<rbrace>
     seL4_GetIPCBuffer'
   \<lbrace>\<lambda>r s. r = heap_seL4_IPCBuffer__C'ptr s (Ptr (scast seL4_GlobalsFrame)) \<and>
          s = s'\<rbrace>!"
  apply (rule allI)
  apply (simp add:seL4_GetIPCBuffer'_def)
  apply wp
  apply (clarsimp simp:globals_frame_intact_def)
  done

lemmas seL4_GetIPCBuffer_wp[wp_unsafe] =
  seL4_GetIPCBuffer_wp'[THEN validNF_make_schematic_post, simplified]

lemma seL4_SetMR_wp[wp_unsafe]:
  notes seL4_SetMR_axiom[simp]
  shows
  "\<lbrace>\<lambda>s. globals_frame_intact s \<and>
        ipc_buffer_valid s \<and>
        i \<ge> 0 \<and>
        i < uint seL4_MsgMaxLength \<and>
        (\<forall>x. P x (setMR s (nat i) v))\<rbrace>
     exec_concrete lift_global_heap (seL4_SetMR' i v)
   \<lbrace>P\<rbrace>!"
  apply (simp add:seL4_SetMR_lifted'_def)
  apply (wp seL4_GetIPCBuffer_wp)
  apply (simp add:setMR_def globals_frame_intact_def ipc_buffer_valid_def)
  done

lemma seL4_GetMR_wp[wp_unsafe]:
  "\<lbrace>\<lambda>s. \<forall>x. i \<ge> 0 \<and>
            i < uint seL4_MsgMaxLength \<and>
            globals_frame_intact s \<and>
            ipc_buffer_valid s \<and>
            P x s\<rbrace>
     seL4_GetMR' i
   \<lbrace>P\<rbrace>!"
  apply (simp add:seL4_GetMR'_def)
  apply (wp seL4_GetIPCBuffer_wp)
  apply (simp add:globals_frame_intact_def ipc_buffer_valid_def seL4_MsgMaxLength_def)
  done

lemma seL4_Wait_wp[wp_unsafe]:
  "\<lbrace>\<lambda>s. globals_frame_intact s \<and>
        ipc_buffer_valid s \<and>
        (\<forall>x v0 v1 v2 v3. P x (setMRs s v0 v1 v2 v3))\<rbrace>
     seL4_Wait' cap NULL
   \<lbrace>P\<rbrace>!"
  apply (simp add:seL4_Wait'_def)
  apply (wp seL4_SetMR_wp)
  apply (simp add:globals_frame_intact_def ipc_buffer_valid_def setMRs_def
                  setMR_def seL4_MsgMaxLength_def)
  done

lemma seL4_ReplyWait_wp[wp_unsafe]:
  "\<lbrace>\<lambda>s. globals_frame_intact s \<and>
        ipc_buffer_valid s \<and>
        (\<forall>x v0 v1 v2 v3. P x (setMRs s v0 v1 v2 v3))\<rbrace>
     seL4_ReplyWait' cap info NULL
   \<lbrace>P\<rbrace>!"
  apply (simp add:seL4_ReplyWait'_def seL4_GetMR'_def)
  apply (wp seL4_SetMR_wp seL4_GetIPCBuffer_wp)
  apply (simp add:globals_frame_intact_def ipc_buffer_valid_def setMRs_def
                  setMR_def seL4_MsgMaxLength_def)
  done

lemma camkes_get_tls_wp':
  "\<forall>s'. \<lbrace>\<lambda>s. tls_valid s \<and> globals_frame_intact s \<and> s = s'\<rbrace>
     camkes_get_tls'
   \<lbrace>\<lambda>r s. s = s' \<and> r = tls_ptr s\<rbrace>!"
  apply (rule allI)
  apply (simp add:camkes_get_tls'_def seL4_GetIPCBuffer'_def tls_valid_def)
  apply wp
  apply (clarsimp simp:globals_frame_intact_def tls_ptr_def)
  done

lemmas camkes_get_tls'_wp[wp] =
  camkes_get_tls_wp'[THEN validNF_make_schematic_post, simplified]
(*>*)

/*# See below for the relevance of this. #*/
/*- set update_global_emitted = set() -*/

text {*
  The generated definitions and lemmas in this chapter have been formed from the same procedure
  specification provided in the previous chapter. Again, to give some context to the proofs below,
  the generated receiving code for the \code{echo\_int} method is given here.
  \clisting{to-echo-int.c}

  The glue code receiving an RPC invocation from another component unmarshals arguments and then
  invokes the user's interface implementation. To show the safety of this glue code we assume that
  the user's implementation being invoked does not modify the state of the system. For example, for
  the \code{echo\_int} method, we assume the following property.

  @{term "\<lbrace>\<lambda>s. \<forall>r. P r s\<rbrace> RPCTo_echo_int' i \<lbrace>P\<rbrace>!"}

  The unbound variables in the above statement, @{term P} and @{term i}, unify
  with any suitably typed expression to allow use of the assumption in all contexts. This property
  states that the
  user's implementation, \code{RPCTo\_echo\_int}, only manipulates local variables and does not
  write to any global memory. The property we ultimately need from the user's implementation is
  weaker than this; that the function does not invalidate the TLS memory. In future the assumption
  above will be reduced to this, but for now we assume this stronger property.
*}

text {*
  For each thread-local variable, a function to retrieve a pointer to the relevant memory for the
  current thread is emitted. For each of these we generate a proof that it does not modify the
  state. This is uninteresting, in and of itself, but useful for reasoning about glue code that
  calls these.
*}
text {* \newpage *}
/*- set commented = [] -*/
/*- for m in me.interface.type.methods -*/

/*- for p in m.parameters -*/
(** TPP: condense = True *)
lemma get_/*? m.name ?*/_/*? p.name ?*/_nf:
  /*- set inv_state = isabelle_symbol('s') -*/
  "\<forall>/*? inv_state ?*/.
    /*- set state = isabelle_symbol('s') -*/
    \<lbrace>\<lambda>/*? state ?*/. globals_frame_intact /*? state ?*/ \<and>
      ipc_buffer_valid /*? state ?*/ \<and>
      tls_valid /*? state ?*/ \<and>
      thread_index_C (tls /*? state ?*/) \<in> {1..thread_count} \<and>
      /*- for t in six.moves.range(threads) -*/
        is_valid_w/*? macros.sizeof(options.architecture, p) * 8 ?*/ /*? state ?*/ (Ptr (symbol_table ''/*? m.name ?*/_/*? p.name ?*/_/*? t + 1 ?*/'')) \<and>
      /*- endfor -*/
      /*? state ?*/ = /*? inv_state ?*/\<rbrace>
     get_/*? m.name ?*/_/*? p.name ?*/'
    /*- set ret = isabelle_symbol('r') -*/
(** TPP: accumulate = True *)
    \<lbrace>\<lambda>/*? ret ?*/ /*? state ?*/.
      /*? ret ?*/ \<in> {
      /*- for t in six.moves.range(threads) -*/
        Ptr (symbol_table ''/*? m.name ?*/_/*? p.name ?*/_/*? t + 1 ?*/'')
        /*- if not loop.last -*/
          ,
        /*- endif -*/
      /*- endfor -*/} \<and>
(** TPP: accumulate = False *)
      /*? state ?*/ = /*? inv_state ?*/\<rbrace>!"
(** TPP: condense = False *)
  apply (rule allI)
  apply (simp add:get_/*? m.name ?*/_/*? p.name ?*/'_def)
  apply (wp seL4_GetIPCBuffer_wp)
  apply (clarsimp simp:thread_count_def tls_valid_def tls_def)
  apply unat_arith
  done
/*- if not commented -*/
    (*<*)
    /*- do commented.append(True) -*/ /*# Gah! #*/
/*- endif -*/

lemmas get_/*? m.name ?*/_/*? p.name ?*/_wp[wp_unsafe] =
  get_/*? m.name ?*/_/*? p.name ?*/_nf[THEN validNF_make_schematic_post, simplified]

/*# Each method parameter necessitates a set of TLS globals. Each of these TLS globals has an
 *# associated heap of variables of that size. E.g. int globals live in the word32 heap. Here we
 *# emit any global update functions we'll be using later, but we need to keep track of which ones
 *# we've already emitted (on behalf of previous parameters). Essentially we want to do this
 *# dynamically rather than emitting these global update functions because (a) we don't want the
 *# ones we don't need and (b) we may have dynamic sized heaps in future.
 #*/
/*- set width = macros.sizeof(options.architecture, p) * 8 -*/
/*- if width not in update_global_emitted -*/
definition
  update_global_w/*? width ?*/ :: "char list \<Rightarrow> word32 \<Rightarrow> lifted_globals \<Rightarrow> lifted_globals"
where
  "update_global_w/*? width ?*/ symbol v s \<equiv>
     heap_w/*? width ?*/_update (\<lambda>c. c(Ptr (symbol_table symbol) := (ucast v))) s"
/*- if width > macros.sizeof(options.architecture, 'void*') * 8 -*/
/*# For types of a greater width than word-size-bits, we need a separate definition for setting the
 *# high bits.
 #*/
definition
  update_global_w/*? width ?*/_high :: "char list \<Rightarrow> word32 \<Rightarrow> lifted_globals \<Rightarrow> lifted_globals"
where
  "update_global_w/*? width ?*/_high symbol high s \<equiv>
     heap_w/*? width ?*/_update (\<lambda>c. c(Ptr (symbol_table symbol) :=
       (heap_w/*? width ?*/ s (Ptr (symbol_table symbol))) || (ucast high << 32))) s"
/*- endif -*/
/*- do update_global_emitted.add(width) -*/
/*- endif -*/

/*- endfor -*/
/*- endfor -*/

(*>*)
text {*
  For each method in the procedure we generate a function for specifically handling receiving of a
  call to that method. A top-level dispatch function is generated that selects the appropriate
  handler to invoke after receiving an RPC invocation. The handler function for the first method is
  the code given at the start of this chapter. We generate proofs that the handler
  functions do not fail, as given below.
*}
/*- for m in me.interface.type.methods -*/

(** TPP: condense = True *)
lemma "/*? thy ?*/_/*? m.name ?*/_internal_nf":
  notes seL4_GetMR_wp[wp] seL4_SetMR_wp[wp]
  shows
  /*- set state0 = isabelle_symbol('s0') -*/
  /*- set state = isabelle_symbol('s') -*/
  "\<forall>/*? state0 ?*/. \<lbrace>\<lambda>/*? state ?*/. inv /*? state ?*/\<rbrace>
    /*? thy ?*/_/*? m.name ?*/_internal'
  /*- set ret = isabelle_symbol('r') -*/
   \<lbrace>\<lambda>/*? ret ?*/ /*? state ?*/. inv /*? state ?*/\<rbrace>!"
  apply (simp add:/*? thy ?*/_/*? m.name ?*/_internal'_def)
  apply wp
       apply (simp add:/*? thy ?*/_/*? m.name ?*/_marshal'_def)
       apply wp
      apply (simp add:/*? thy ?*/_/*? m.name ?*/_invoke'_def)
      apply (wp /*? thy ?*/_/*? m.name ?*/_wp)
   apply (simp add:/*? thy ?*/_/*? m.name ?*/_unmarshal'_def)
   /*# This time it is important to reverse the parameter list because WP has flipped our TLS
    *# retrieval code.
    #*/
   /*- for p in reversed(m.parameters) -*/
   apply (wp get_/*? m.name ?*/_/*? p.name ?*/_wp)
   /*- endfor -*/
  apply (clarsimp simp:seL4_MsgMaxLength_def|unfold inv_def, clarsimp|rule conjI, clarsimp|drule /*? me.interface.name ?*/_/*? m.name ?*/_inv)+
  done
(** TPP: condense = False *)

lemmas "/*? thy ?*/_/*? m.name ?*/_internal_wp"[wp_unsafe] =
  "/*? thy ?*/_/*? m.name ?*/_internal_nf"[THEN validNF_make_schematic_post, simplified]

/*- endfor -*/

text {*
  \newpage
  With proofs that the handler functions do not fail, the proof of the same for the top-level
  dispatch function can be generated by composing these. Note that we accumulate the pre- and
  post-conditions from the leaf functions.
*}

(** TPP: condense = True *)
lemma "/*? thy ?*/_run_internal_wp"[wp_unsafe]:
  notes seL4_SetMR_axiom[simp] seL4_SetMR_wp[wp] seL4_GetMR_wp[wp]
  /*- set state = isabelle_symbol('s') -*/
  shows
  "\<lbrace>\<lambda>/*? state ?*/. globals_frame_intact /*? state ?*/ \<and>

  tls_valid /*? state ?*/ \<and>
  thread_index_C (tls /*? state ?*/) \<in> {1..thread_count} \<and>

  /*- for m in me.interface.type.methods -*/
    /*- for p in m.parameters -*/
      /*- for t in six.moves.range(threads) -*/
        is_valid_w/*? macros.sizeof(options.architecture, p) * 8 ?*/ /*? state ?*/ (Ptr (symbol_table ''/*? m.name ?*/_/*? p.name ?*/_/*? t + 1 ?*/'')) \<and>
      /*- endfor -*/
    /*- endfor -*/
  /*- endfor -*/

  ipc_buffer_valid /*? state ?*/\<rbrace>
    /*- set first = isabelle_symbol('first') -*/
    /*- set info = isabelle_symbol('info') -*/
    /*? thy ?*/__run_internal' /*? first ?*/ /*? info ?*/
  \<lbrace>\<lambda>_ /*? state ?*/. globals_frame_intact /*? state ?*/ \<and>

  tls_valid /*? state ?*/ \<and>
  thread_index_C (tls /*? state ?*/) \<in> {1..thread_count} \<and>

  /*- for m in me.interface.type.methods -*/
    /*- for p in m.parameters -*/
      /*- for t in six.moves.range(threads) -*/
        is_valid_w/*? macros.sizeof(options.architecture, p) * 8 ?*/ /*? state ?*/ (Ptr (symbol_table ''/*? m.name ?*/_/*? p.name ?*/_/*? t + 1 ?*/'')) \<and>
      /*- endfor -*/
    /*- endfor -*/
  /*- endfor -*/
  ipc_buffer_valid /*? state ?*/\<rbrace>!"
  apply (simp add:/*? me.interface.name ?*/__run_internal'_def)
  apply wp
  /*- for m in me.interface.type.methods -*/
       apply (wp seL4_ReplyWait_wp)
      apply (simp add:seL4_MessageInfo_new'_def)
      apply wp
     apply (wp /*? thy ?*/_/*? m.name ?*/_internal_wp)
  /*- endfor -*/
    apply (wp seL4_Wait_wp)
(** TPP: accumulate = True *)
  apply (clarsimp simp:globals_frame_intact_def ipc_buffer_valid_def
                       tls_valid_def tls_def tls_ptr_def ucast_id
                       seL4_GetIPCBuffer'_def thread_count_def
                       setMR_def setMRs_def inv_def seL4_MsgMaxLength_def
  /*- set update_global_used = set() -*/
  /*- for m in me.interface.type.methods -*/
    /*- for p in m.parameters -*/
      /*- set width = macros.sizeof(options.architecture, p) * 8 -*/
      /*- if width not in update_global_used -*/
        update_global_w/*? width ?*/_def
        /*- if width > macros.sizeof(options.architecture, 'void*') * 8 -*/
          update_global_w/*? width ?*/_high_def
        /*- endif -*/
        /*- do update_global_used.add(width) -*/
      /*- endif -*/
    /*- endfor -*/
  /*- endfor -*/
  )
(** TPP: accumulate = False *)
  done
(** TPP: condense = False *)

(*<*)
end

end
(*>*)
