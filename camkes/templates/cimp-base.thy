/*#
 *# Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *#
 *# SPDX-License-Identifier: BSD-2-Clause
 #*/

(* /*? macros.generated_file_notice() ?*/ *)

/*? macros.check_isabelle_outfile(
        '%s_Cimp_Base' % options.verification_base_name, outfile_name) ?*/

theory "/*? options.verification_base_name ?*/_Cimp_Base" imports
  "CamkesGlueSpec.Types"
  "CamkesGlueSpec.Abbreviations"
  "CamkesGlueSpec.Connector"
begin

/*- macro show_native_type(type) --*/
    /*-- if type in ['int', 'int8_t', 'int16_t', 'int32_t', 'int64_t'] --*/
        int
    /*-- elif type in ['unsigned int', 'uint8_t', 'uint16_t', 'uint32_t', 'uint64_t', 'uintptr_t'] --*/
        nat
    /*-- elif type in ['char', 'character'] --*/
        char
    /*-- elif type == 'bool' --*/
        bool
    /*-- elif type == 'string' --*/
        string
    /*-- else --*/
        /*? raise(TemplateError('unsupported native type: %s' % type)) ?*/
    /*-- endif --*/
/*-- endmacro -*/

/*- macro show_wrapped_type(type) --*/
    /*-- if type in ['int', 'int8_t', 'int16_t', 'int32_t', 'int64_t'] --*/
        Integer
    /*-- elif type in ['unsigned int', 'uint8_t', 'uint16_t', 'uint32_t', 'uint64_t', 'uintptr_t'] --*/
        Number
    /*-- elif type in ['char', 'character'] --*/
        Char
    /*-- elif type == 'bool' --*/
        Boolean
    /*-- elif type == 'string' --*/
        String
    /*-- else --*/
        /*? raise(TemplateError('unsupported wrapped type: %s' % type)) ?*/
    /*-- endif --*/
/*-- endmacro -*/

/*- set instances = composition.instances -*/
/*- set connections = composition.connections -*/
/*- set components = set(map(lambda('x: x.type'), instances)) -*/

(** TPP: condense = True *)
(* Connections *)
datatype channel
/*- for c in connections -*/
  /*- if loop.first --*/
    =
  /*-- else --*/
    |
  /*-- endif -*/ /*? c.name ?*/
/*- endfor -*/
(** TPP: condense = False *)

(** TPP: condense = True *)
(* Component instances *)
datatype inst
/*- for i in instances -*/
  /*- if loop.first --*/
    =
  /*-- else --*/
    |
  /*-- endif -*/ /*? i.name ?*/
/*- endfor -*/
/*- for c in connections -*/
  /*- if c.type.from_type == 'Event' -*/
  | /*? c.name ?*/\<^sub>e
  /*- elif c.type.from_type == 'Dataport' -*/
  | /*? c.name ?*/\<^sub>d
  /*- endif -*/
/*- endfor -*/
(** TPP: condense = False *)

/*- for c in components -*/

(** TPP: condense = True *)
(* /*? c.name ?*/'s interfaces *)
datatype /*? c.name ?*/_channel
/*- for i in c.uses + c.provides + c.emits + c.consumes + c.dataports -*/
  /*- if loop.first --*/
    =
  /*-- else --*/
    |
  /*-- endif -*/ /*? c.name ?*/_/*? i.name ?*/
/*- endfor -*/
(** TPP: condense = False *)

    /*# Glue code for each outgoing procedural interface. #*/
    /*- for u in c.uses -*/
        /*- for i, m in enumerate(u.type.methods) -*/
(** TPP: condense = True *)
definition
  /*- set type_sig = ['(%s_channel \\<Rightarrow> channel) \\<Rightarrow>' % c.name] -*/
  /*- for p in filter(lambda('x: x.direction in [\'in\', \'inout\']'), m.parameters) -*/
    /*- do type_sig.append('(\'cs local_state \\<Rightarrow> %s) \\<Rightarrow>' % show_native_type(p.type)) -*/
  /*- endfor -*/
  /*- if m.return_type is not none or len(list(filter(lambda('x: x.direction in [\'out\', \'inout\']'), m.parameters))) > 0 -*/
    /*- do type_sig.append('(\'cs local_state') -*/
  /*- endif -*/
  /*- if m.return_type is not none -*/
    /*- do type_sig.append('\\<Rightarrow> %s' % show_native_type(m.return_type)) -*/
  /*- endif -*/
  /*- for p in filter(lambda('x: x.direction in [\'out\', \'inout\']'), m.parameters) -*/
    /*- do type_sig.append('\\<Rightarrow> %s' % show_native_type(p.type)) -*/
  /*- endfor -*/
  /*- if m.return_type is not none or len(list(filter(lambda('x: x.direction in [\'out\', \'inout\']'), m.parameters))) > 0 -*/
      /*# We had to unmarshal at least one parameter. #*/
      /*- do type_sig.append('\\<Rightarrow> \'cs local_state) \\<Rightarrow>') -*/
  /*- endif -*/
  /*- do type_sig.append('(channel, \'cs) comp') -*/
  Call_/*? c.name ?*/_/*? u.name ?*/_/*? m.name ?*/ :: "/*? ' '.join(type_sig) ?*/"
where
  /*- set ch = isabelle_symbol('ch') -*/
  /*- set params = [ch] -*/
  /*- for p in filter(lambda('x: x.direction in [\'in\', \'inout\']'), m.parameters) -*/
    /*- do params.append('%s\\<^sub>P' % p.name) -*/
  /*- endfor -*/
  /*- if m.return_type is not none or len(list(filter(lambda('x: x.direction in [\'out\', \'inout\']'), m.parameters))) > 0 -*/
    /*- do params.append('embed_ret') -*/
  /*- endif -*/
  "Call_/*? c.name ?*/_/*? u.name ?*/_/*? m.name ?*/ /*? ' '.join(params) ?*/
  /*-- set s = isabelle_symbol('s') --*/
  \<equiv> Request (\<lambda>/*? s ?*/. {\<lparr>q_channel = /*? ch ?*/ /*? c.name ?*/_/*? u.name ?*/, q_data = Call /*? i ?*/ (
  /*- for p in filter(lambda('x: x.direction in [\'in\', \'inout\']'), m.parameters) -*/
      /*? show_wrapped_type(p.type) ?*/ (/*? p.name ?*/\<^sub>P /*? s ?*/) #
  /*- endfor -*/
  [])\<rparr>}) discard ;;
  /*- set q = isabelle_symbol() -*/
  /*- set s = isabelle_symbol() -*/
  /*- set xs = isabelle_symbol() -*/
  Response (\<lambda>/*? q ?*/ /*? s ?*/. case q_data /*? q ?*/ of Return /*? xs ?*/ \<Rightarrow>
  /*- if m.return_type is not none or len(list(filter(lambda('x: x.direction in [\'out\', \'inout\']'), m.parameters))) > 0 -*/
      {(embed_ret /*? s ?*/
      /*- if m.return_type is not none -*/
          /*- set v = isabelle_symbol() -*/
          (case hd /*? xs ?*/ of /*? show_wrapped_type(m.return_type) ?*/ /*? v ?*/ \<Rightarrow> /*? v ?*/)
      /*- endif -*/
      /*- for i, p in enumerate(filter(lambda('x: x.direction in [\'out\', \'inout\']'), m.parameters)) -*/
          /*- set v = isabelle_symbol() -*/
          (case /*? xs ?*/ ! /*? i + (1 if m.return_type is not none else 0) ?*/ of /*? show_wrapped_type(p.type) ?*/ /*? v ?*/ \<Rightarrow> /*? v ?*/)
      /*- endfor -*/
  /*- else -*/
      {(/*? s ?*/
  /*- endif -*/
  , \<lparr>a_channel = /*? ch ?*/ /*? c.name ?*/_/*? u.name ?*/, a_data = Void\<rparr>)} | _ \<Rightarrow> {})"
(** TPP: condense = False *)
        /*- endfor -*/
    /*- endfor -*/

    /*# Glue code for each incoming procedural interface. #*/
    /*- for u in c.provides -*/
(** TPP: condense = True *)
definition
  /*- set type_sig = ['(%s_channel \\<Rightarrow> channel) \\<Rightarrow>' % c.name] -*/
  /*- for m in u.type.methods -*/
    /*- if len(list(filter(lambda('x: x.direction in [\'in\', \'inout\']'), m.parameters))) > 0 -*/
      /*- do type_sig.append('(\'cs local_state \\<Rightarrow>') -*/
      /*- for p in filter(lambda('x: x.direction in [\'in\', \'inout\']'), m.parameters) -*/
        /*- do type_sig.append('%s \\<Rightarrow>' % show_native_type(p.type)) -*/
      /*- endfor -*/
      /*- do type_sig.append('\'cs local_state) \\<Rightarrow>') -*/
    /*- endif -*/
    /*- do type_sig.append('(channel, \'cs) comp \\<Rightarrow>') -*/
    /*- if m.return_type is not none -*/
      /*- do type_sig.append('(\'cs local_state \\<Rightarrow> %s) \\<Rightarrow>' % show_native_type(m.return_type)) -*/
    /*- endif -*/
    /*- for p in filter(lambda('x: x.direction in [\'out\', \'inout\']'), m.parameters) -*/
      /*- do type_sig.append('(\'cs local_state \\<Rightarrow> %s) \\<Rightarrow>' % show_native_type(p.type)) -*/
    /*- endfor -*/
  /*- endfor -*/
  /*- do type_sig.append('(channel, \'cs) comp') -*/
  Recv_/*? c.name ?*/_/*? u.name ?*/ :: "/*? ' '.join(type_sig) ?*/"
where
  /*- set ch = isabelle_symbol('ch') -*/
  /*- set params = [ch] -*/
  /*- for m in u.type.methods -*/
    /*- if len(list(filter(lambda('x: x.direction in [\'in\', \'inout\']'), m.parameters))) > 0 -*/
      /*- do params.append('%s\\<^sub>E' % m.name) -*/
    /*- endif -*/
    /*- do params.append('%s_%s_%s' % (c.name, u.name, m.name)) -*/
    /*- if m.return_type is not none -*/
      /*- do params.append('%s_return\\<^sub>P' % m.name) -*/
    /*- endif -*/
    /*- for p in filter(lambda('x: x.direction in [\'out\', \'inout\']'), m.parameters) -*/
      /*- do params.append('%s_%s\\<^sub>P' % (m.name, p.name)) -*/
    /*- endfor -*/
  /*- endfor -*/
  "Recv_/*? c.name ?*/_/*? u.name ?*/ /*? ' '.join(params) ?*/
  \<equiv>
  /*- for i, m in enumerate(u.type.methods) -*/
      /*- if not loop.first -*/
          \<squnion>
      /*- endif -*/
      /*- set q = isabelle_symbol() -*/
      /*- set s = isabelle_symbol() -*/
      /*- set n = isabelle_symbol() -*/
      /*- set xs = isabelle_symbol() -*/
      (Response (\<lambda>/*? q ?*/ /*? s ?*/. case q_data /*? q ?*/ of Call /*? n ?*/ /*? xs ?*/ \<Rightarrow> (if /*? n ?*/ = /*? i ?*/ then {(
      /*- if len(list(filter(lambda('x: x.direction in [\'in\', \'inout\']'), m.parameters))) > 0 -*/
          /*? m.name ?*/\<^sub>E /*? s ?*/
          /*- for k, p in enumerate(filter(lambda('x: x.direction in [\'in\', \'inout\']'), m.parameters)) -*/
              /*- set v = isabelle_symbol() -*/
              (case /*? xs ?*/ ! /*? k ?*/ of /*? show_wrapped_type(p.type) ?*/ /*? v ?*/ \<Rightarrow> /*? v ?*/)
          /*- endfor -*/
      /*- else -*/
          /*? s ?*/
      /*- endif -*/
      , \<lparr>a_channel = /*? ch ?*/ /*? c.name ?*/_/*? u.name ?*/, a_data = Void\<rparr>)} else {}) | _ \<Rightarrow> {}) ;;
      /*? c.name ?*/_/*? u.name ?*/_/*? m.name ?*/ ;;
      /*- set s = isabelle_symbol() -*/
      Request (\<lambda>/*? s ?*/. {\<lparr>q_channel = /*? ch ?*/ /*? c.name ?*/_/*? u.name ?*/, q_data = Return (
      /*- if m.return_type is not none -*/
          /*? show_wrapped_type(m.return_type) ?*/ (/*? m.name ?*/_return\<^sub>P /*? s ?*/) #
      /*- endif -*/
      /*- for p in filter(lambda('x: x.direction in [\'out\', \'inout\']'), m.parameters) -*/
          /*? show_wrapped_type(p.type) ?*/ (/*? m.name ?*/_/*? p.name ?*/\<^sub>P /*? s ?*/) #
      /*- endfor -*/
      [])\<rparr>}) discard)
  /*- endfor -*/
  "
(** TPP: condense = False *)
    /*- endfor -*/

    /*# Glue code for each outgoing event interface. #*/
    /*- for u in c.emits -*/
(** TPP: condense = True *)
definition
  Emit_/*? c.name ?*/_/*? u.name ?*/ :: "(/*? c.name ?*/_channel \<Rightarrow> channel) \<Rightarrow> (channel, 'cs) comp"
where
  /*- set ch = isabelle_symbol('ch') -*/
  "Emit_/*? c.name ?*/_/*? u.name ?*/ /*? ch ?*/ \<equiv> EventEmit (/*? ch ?*/ /*? c.name ?*/_/*? u.name ?*/)"
(** TPP: condense = False *)
    /*- endfor -*/

    /*# Glue code for each incoming event interface. #*/
    /*- for u in c.consumes -*/
(** TPP: condense = True *)
definition
  Poll_/*? c.name ?*/_/*? u.name ?*/ :: "(/*? c.name ?*/_channel \<Rightarrow> channel) \<Rightarrow> ('cs local_state \<Rightarrow> bool \<Rightarrow> 'cs local_state) \<Rightarrow> (channel, 'cs) comp"
where
  /*- set ch = isabelle_symbol('ch') -*/
  /*- set embed = isabelle_symbol('embed') -*/
  "Poll_/*? c.name ?*/_/*? u.name ?*/ /*? ch ?*/ /*? embed ?*/ \<equiv> EventPoll (/*? ch ?*/ /*? c.name ?*/_/*? u.name ?*/) /*? embed ?*/"
(** TPP: condense = False *)

(** TPP: condense = True *)
definition
  Wait_/*? c.name ?*/_/*? u.name ?*/ :: "(/*? c.name ?*/_channel \<Rightarrow> channel) \<Rightarrow> ('cs local_state \<Rightarrow> bool \<Rightarrow> 'cs local_state) \<Rightarrow> (channel, 'cs) comp"
where
  /*- set embed = isabelle_symbol('embed') -*/
  "Wait_/*? c.name ?*/_/*? u.name ?*/ /*? ch ?*/ /*? embed ?*/ \<equiv> EventWait (/*? ch ?*/ /*? c.name ?*/_/*? u.name ?*/) /*? embed ?*/"
(** TPP: condense = False *)
    /*- endfor -*/

    /*# Glue code for dataport interfaces. #*/
    /*- for u in c.dataports -*/
(** TPP: condense = True *)
definition
  Read_/*? c.name ?*/_/*? u.name ?*/ :: "(/*? c.name ?*/_channel \<Rightarrow> channel) \<Rightarrow> ('cs local_state \<Rightarrow> nat) \<Rightarrow> ('cs local_state \<Rightarrow> variable \<Rightarrow> 'cs local_state) \<Rightarrow> (channel, 'cs) comp"
where
  /*- set ch = isabelle_symbol('ch') -*/
  /*- set addr = isabelle_symbol('addr') -*/
  /*- set embed = isabelle_symbol('embed') -*/
  "Read_/*? c.name ?*/_/*? u.name ?*/ /*? ch ?*/ /*? addr ?*/ /*? embed ?*/ \<equiv> MemoryRead (/*? ch ?*/ /*? c.name ?*/_/*? u.name ?*/) /*? addr ?*/ /*? embed ?*/"
(** TPP: condense = False *)

(** TPP: condense = True *)
definition
  Write_/*? c.name ?*/_/*? u.name ?*/ :: "(/*? c.name ?*/_channel \<Rightarrow> channel) \<Rightarrow> ('cs local_state \<Rightarrow> nat) \<Rightarrow> ('cs local_state \<Rightarrow> variable) \<Rightarrow> (channel, 'cs) comp"
where
  /*- set ch = isabelle_symbol('ch') -*/
  /*- set addr = isabelle_symbol('addr') -*/
  /*- set proj = isabelle_symbol('proj') -*/
  "Write_/*? c.name ?*/_/*? u.name ?*/ /*? ch ?*/ /*? addr ?*/ /*? proj ?*/ \<equiv> MemoryWrite (/*? ch ?*/ /*? c.name ?*/_/*? u.name ?*/) /*? addr ?*/ /*? proj ?*/"
(** TPP: condense = False *)
    /*- endfor -*/

/*- endfor -*/

(* Component instantiations *)
/*- for i in instances -*/
    /*- set c = i.type -*/

    /*- for u in c.uses -*/
        /*- for m in u.type.methods -*/
(** TPP: condense = True *)
definition
  /*- set type_sig = [] -*/
  /*- for p in filter(lambda('x: x.direction in [\'in\', \'inout\']'), m.parameters) -*/
    /*- do type_sig.append('(\'cs local_state \\<Rightarrow> %s) \\<Rightarrow>' % show_native_type(p.type)) -*/
  /*- endfor -*/
  /*- if m.return_type is not none or len(list(filter(lambda('x: x.direction in [\'out\', \'inout\']'), m.parameters))) > 0 -*/
    /*- do type_sig.append('(\'cs local_state') -*/
  /*- endif -*/
  /*- if m.return_type is not none -*/
    /*- do type_sig.append('\\<Rightarrow> %s' % show_native_type(m.return_type)) -*/
  /*- endif -*/
  /*- for p in filter(lambda('x: x.direction in [\'out\', \'inout\']'), m.parameters) -*/
    /*- do type_sig.append('\\<Rightarrow> %s' % show_native_type(p.type)) -*/
  /*- endfor -*/
  /*- if m.return_type is not none or len(list(filter(lambda('x: x.direction in [\'out\', \'inout\']'), m.parameters))) > 0 -*/
    /*# We had to unmarshal at least one parameter. #*/
    /*- do type_sig.append('\\<Rightarrow> \'cs local_state) \\<Rightarrow>') -*/
  /*- endif -*/
  /*- do type_sig.append('(channel, \'cs) comp') -*/
  Call_/*? i.name ?*/_/*? u.name ?*/_/*? m.name ?*/ :: "/*? ' '.join(type_sig) ?*/"
where
  "Call_/*? i.name ?*/_/*? u.name ?*/_/*? m.name ?*/ \<equiv>
      /*- set l = isabelle_symbol() -*/
      Call_/*? c.name ?*/_/*? u.name ?*/_/*? m.name ?*/ (\<lambda>/*? l ?*/. case /*? l ?*/ of
      /*- set j = joiner('|') -*/
      /*- for conn in connections -*/
          /*- set idx = eval('[ idx for idx in range(len(conn.from_ends)) if i.name == conn.from_ends[idx].instance.name ]', {'i': i, 'conn': conn}) -*/
          /*- if idx -*/
              /*? j() ?*/ /*? c.name ?*/_/*? conn.from_ends[idx[0]].interface.name ?*/ \<Rightarrow> /*? conn.name ?*/
          /*- endif -*/
          /*- set idx = eval('[ idx for idx in range(len(conn.to_ends)) if i.name == conn.to_ends[idx].instance.name ]', {'i': i, 'conn': conn}) -*/
          /*- if idx -*/
              /*? j() ?*/ /*? c.name ?*/_/*? conn.to_ends[idx[0]].interface.name ?*/ \<Rightarrow> /*? conn.name ?*/
          /*- endif -*/
      /*- endfor -*/
      )"
(** TPP: condense = False *)
        /*- endfor -*/
    /*- endfor -*/

    /*- for u in c.provides -*/
(** TPP: condense = True *)
definition
  /*- set type_sig = [] -*/
  /*- for m in u.type.methods -*/
    /*- if len(list(filter(lambda('x: x.direction in [\'in\', \'inout\']'), m.parameters))) > 0 -*/
      /*- do type_sig.append('(\'cs local_state \\<Rightarrow>') -*/
      /*- for p in filter(lambda('x: x.direction in [\'in\', \'inout\']'), m.parameters) -*/
        /*- do type_sig.append('%s \\<Rightarrow>' % show_native_type(p.type)) -*/
      /*- endfor -*/
      /*- do type_sig.append('\'cs local_state) \\<Rightarrow>') -*/
    /*- endif -*/
    /*- do type_sig.append('(channel, \'cs) comp \\<Rightarrow>') -*/
    /*- if m.return_type -*/
      /*- do type_sig.append('(\'cs local_state \\<Rightarrow> %s) \\<Rightarrow>' % show_native_type(m.return_type)) -*/
    /*- endif -*/
    /*- for p in filter(lambda('x: x.direction in [\'out\', \'inout\']'), m.parameters) -*/
      /*- do type_sig.append('(\'cs local_state \\<Rightarrow> %s) \\<Rightarrow>' % show_native_type(p.type)) -*/
    /*- endfor -*/
  /*- endfor -*/
  /*- do type_sig.append('(channel, \'cs) comp') -*/
  Recv_/*? i.name ?*/_/*? u.name ?*/ :: "/*? ' '.join(type_sig) ?*/"
where
  "Recv_/*? i.name ?*/_/*? u.name ?*/ \<equiv>
      /*- set l = isabelle_symbol() -*/
      Recv_/*? c.name ?*/_/*? u.name ?*/ (\<lambda>/*? l ?*/. case /*? l ?*/ of
      /*- set j = joiner('|') -*/
      /*- for conn in connections -*/
          /*- set idx = eval('[ idx for idx in range(len(conn.from_ends)) if i.name == conn.from_ends[idx].instance.name ]', {'i': i, 'conn': conn}) -*/
          /*- if idx -*/
              /*? j() ?*/ /*? c.name ?*/_/*? conn.from_ends[idx[0]].interface.name ?*/ \<Rightarrow> /*? conn.name ?*/
          /*- endif -*/
          /*- set idx = eval('[ idx for idx in range(len(conn.to_ends)) if i.name == conn.to_ends[idx].instance.name ]', {'i': i, 'conn': conn}) -*/
          /*- if idx -*/
              /*? j() ?*/ /*? c.name ?*/_/*? conn.to_ends[idx[0]].interface.name ?*/ \<Rightarrow> /*? conn.name ?*/
          /*- endif -*/
      /*- endfor -*/
      )"
(** TPP: condense = False *)
    /*- endfor -*/

    /*- for u in c.emits -*/
(** TPP: condense = True *)
definition
  Emit_/*? i.name ?*/_/*? u.name ?*/ :: "(channel, 'cs) comp"
where
  /*- set l = isabelle_symbol() -*/
  "Emit_/*? i.name ?*/_/*? u.name ?*/ \<equiv> Emit_/*? c.name ?*/_/*? u.name ?*/ (\<lambda>/*? l ?*/. case /*? l ?*/ of
  /*- set j = joiner('|') -*/
  /*- for conn in connections -*/
      /*- set idx = eval('[ idx for idx in range(len(conn.from_ends)) if i.name == conn.from_ends[idx].instance.name ]', {'i': i, 'conn': conn}) -*/
      /*- if idx -*/
          /*? j() ?*/ /*? c.name ?*/_/*? conn.from_ends[idx[0]].interface.name ?*/ \<Rightarrow> /*? conn.name ?*/
      /*- endif -*/
      /*- set idx = eval('[ idx for idx in range(len(conn.to_ends)) if i.name == conn.to_ends[idx].instance.name ]', {'i': i, 'conn': conn}) -*/
      /*- if idx -*/
          /*? j() ?*/ /*? c.name ?*/_/*? conn.to_ends[idx[0]].interface.name ?*/ \<Rightarrow> /*? conn.name ?*/
      /*- endif -*/
  /*- endfor -*/
  )"
(** TPP: condense = False *)
    /*- endfor -*/

    /*- for u in c.consumes -*/
(** TPP: condense = True *)
definition
  Poll_/*? i.name ?*/_/*? u.name ?*/ :: "('cs local_state \<Rightarrow> bool \<Rightarrow> 'cs local_state) \<Rightarrow> (channel, 'cs) comp"
where
  /*- set l = isabelle_symbol() -*/
  "Poll_/*? i.name ?*/_/*? u.name ?*/ \<equiv> Poll_/*? c.name ?*/_/*? u.name ?*/ (\<lambda>/*? l ?*/. case /*? l ?*/ of
  /*- set j = joiner('|') -*/
  /*- for conn in connections -*/
      /*- set idx = eval('[ idx for idx in range(len(conn.from_ends)) if i.name == conn.from_ends[idx].instance.name ]', {'i': i, 'conn': conn}) -*/
      /*- if idx -*/
          /*? j() ?*/ /*? c.name ?*/_/*? conn.from_ends[idx[0]].interface.name ?*/ \<Rightarrow> /*? conn.name ?*/
      /*- endif -*/
      /*- set idx = eval('[ idx for idx in range(len(conn.to_ends)) if i.name == conn.to_ends[idx].instance.name ]', {'i': i, 'conn': conn}) -*/
      /*- if idx -*/
          /*? j() ?*/ /*? c.name ?*/_/*? conn.to_ends[idx[0]].interface.name ?*/ \<Rightarrow> /*? conn.name ?*/
      /*- endif -*/
  /*- endfor -*/
  )"
(** TPP: condense = False *)

(** TPP: condense = True *)
definition
  Wait_/*? i.name ?*/_/*? u.name ?*/ :: "('cs local_state \<Rightarrow> bool \<Rightarrow> 'cs local_state) \<Rightarrow> (channel, 'cs) comp"
where
  /*- set l = isabelle_symbol() -*/
  "Wait_/*? i.name ?*/_/*? u.name ?*/ \<equiv> Wait_/*? c.name ?*/_/*? u.name ?*/ (\<lambda>/*? l ?*/. case /*? l ?*/ of
  /*- set j = joiner('|') -*/
  /*- for conn in connections -*/
      /*- set idx = eval('[ idx for idx in range(len(conn.from_ends)) if i.name == conn.from_ends[idx].instance.name ]', {'i': i, 'conn': conn}) -*/
      /*- if idx -*/
          /*? j() ?*/ /*? c.name ?*/_/*? conn.from_ends[idx[0]].interface.name ?*/ \<Rightarrow> /*? conn.name ?*/
      /*- endif -*/
      /*- set idx = eval('[ idx for idx in range(len(conn.to_ends)) if i.name == conn.to_ends[idx].instance.name ]', {'i': i, 'conn': conn}) -*/
      /*- if idx -*/
          /*? j() ?*/ /*? c.name ?*/_/*? conn.to_ends[idx[0]].interface.name ?*/ \<Rightarrow> /*? conn.name ?*/
      /*- endif -*/
  /*- endfor -*/
  )"
(** TPP: condense = False *)
    /*- endfor -*/

    /*- for u in c.dataports -*/
(** TPP: condense = True *)
definition
  Read_/*? i.name ?*/_/*? u.name ?*/ :: "('cs local_state \<Rightarrow> nat) \<Rightarrow> ('cs local_state \<Rightarrow> variable \<Rightarrow> 'cs local_state) \<Rightarrow> (channel, 'cs) comp"
where
  /*- set l = isabelle_symbol() -*/
  "Read_/*? i.name ?*/_/*? u.name ?*/ \<equiv> Read_/*? c.name ?*/_/*? u.name ?*/ (\<lambda>/*? l ?*/. case /*? l ?*/ of
  /*- set j = joiner('|') -*/
  /*- for conn in connections -*/
      /*- set idx = eval('[ idx for idx in range(len(conn.from_ends)) if i.name == conn.from_ends[idx].instance.name ]', {'i': i, 'conn': conn}) -*/
      /*- if idx -*/
          /*? j() ?*/ /*? c.name ?*/_/*? conn.from_ends[idx[0]].interface.name ?*/ \<Rightarrow> /*? conn.name ?*/
      /*- endif -*/
      /*- set idx = eval('[ idx for idx in range(len(conn.to_ends)) if i.name == conn.to_ends[idx].instance.name ]', {'i': i, 'conn': conn}) -*/
      /*- if idx -*/
          /*? j() ?*/ /*? c.name ?*/_/*? conn.to_ends[idx[0]].interface.name ?*/ \<Rightarrow> /*? conn.name ?*/
      /*- endif -*/
  /*- endfor -*/
  )"
(** TPP: condense = False *)

(** TPP: condense = True *)
definition
  Write_/*? i.name ?*/_/*? u.name ?*/ :: "('cs local_state \<Rightarrow> nat) \<Rightarrow> ('cs local_state \<Rightarrow> variable) \<Rightarrow> (channel, 'cs) comp"
where
  /*- set l = isabelle_symbol() -*/
  "Write_/*? i.name ?*/_/*? u.name ?*/ \<equiv> Write_/*? c.name ?*/_/*? u.name ?*/ (\<lambda>/*? l ?*/. case /*? l ?*/ of
  /*- set j = joiner('|') -*/
  /*- for conn in connections -*/
      /*- set idx = eval('[ idx for idx in range(len(conn.from_ends)) if i.name == conn.from_ends[idx].instance.name ]', {'i': i, 'conn': conn}) -*/
      /*- if idx -*/
          /*? j() ?*/ /*? c.name ?*/_/*? conn.from_ends[idx[0]].interface.name ?*/ \<Rightarrow> /*? conn.name ?*/
      /*- endif -*/
      /*- set idx = eval('[ idx for idx in range(len(conn.to_ends)) if i.name == conn.to_ends[idx].instance.name ]', {'i': i, 'conn': conn}) -*/
      /*- if idx -*/
          /*? j() ?*/ /*? c.name ?*/_/*? conn.to_ends[idx[0]].interface.name ?*/ \<Rightarrow> /*? conn.name ?*/
      /*- endif -*/
  /*- endfor -*/
  )"
(** TPP: condense = False *)
    /*- endfor -*/

/*- endfor -*/

locale system_state =
  fixes init_component_state :: 'cs
  fixes trusted :: "(inst, ((channel, 'cs) comp \<times> 'cs local_state)) map"
begin

/*- for c in components -*/
    /*# Emit a broad definition for each component if the user does not want to instantiate it. #*/
(** TPP: condense = True *)
definition
  /*? c.name ?*/_untrusted :: "(/*? c.name ?*/_channel \<Rightarrow> channel) \<Rightarrow> (channel, 'cs) comp"
where
  /*- set ch = isabelle_symbol('ch') -*/
  "/*? c.name ?*/_untrusted /*? ch ?*/ \<equiv>
      LOOP (
          UserStep
          /*- for i in c.uses + c.provides + c.emits + c.consumes + c.dataports -*/
              \<squnion> ArbitraryRequest (/*? ch ?*/ /*? c.name ?*/_/*? i.name ?*/)
              \<squnion> ArbitraryResponse (/*? ch ?*/ /*? c.name ?*/_/*? i.name ?*/)
          /*- endfor -*/
      )"
(** TPP: condense = False *)
/*- endfor -*/

/*# Emit simulated components for each event. #*/
/*- for e in reduce(lambda('xs, b: xs + ([b.type] if b.type not in xs else [])'), flatMap(lambda('x: x.emits + x.consumes'), components), []) -*/

(* Simulated component for event /*? e ?*/. *)
type_synonym /*? e ?*/_channel = unit

(** TPP: condense = True *)
definition
  /*? e ?*/ :: "(/*? e ?*/_channel \<Rightarrow> channel) \<Rightarrow> (channel, 'cs) comp"
where
  /*- set ch = isabelle_symbol('ch') -*/
  "/*? e ?*/ /*? ch ?*/ \<equiv> event (/*? ch ?*/ ())"
(** TPP: condense = False *)
/*- endfor -*/

/*# Emit simulated components for each dataport. #*/
/*- for d in reduce(lambda('xs, b: xs + ([b.type] if b.type not in xs else [])'), flatMap(lambda('x: x.dataports'), components), []) -*/
    /*# The built-in type 'Buf' is defined in Connector.thy. #*/
    /*- if d != 'Buf' -*/

type_synonym /*? d ?*/\<^sub>d_channel = unit

(** TPP: condense = True *)
definition
  /*? d ?*/\<^sub>d :: "(/*? d ?*/\<^sub>d_channel \<Rightarrow> channel) \<Rightarrow> (channel, 'cs) comp"
where
  /*- set ch = isabelle_symbol('ch') -*/
  "/*? d ?*/\<^sub>d /*? ch ?*/ \<equiv> memory (/*? ch ?*/ ())"
(** TPP: condense = False *)
    /*- endif -*/
/*- endfor -*/

(* Component instantiations *)
/*- for i in instances -*/
    /*- set c = i.type -*/

(** TPP: condense = True *)
definition
  /*? i.name ?*/_untrusted :: "(channel, 'cs) comp"
where
  /*- set l = isabelle_symbol() -*/
  "/*? i.name ?*/_untrusted \<equiv> /*? c.name ?*/_untrusted (\<lambda>/*? l ?*/. case /*? l ?*/ of
  /*- set j = joiner('|') -*/
  /*- for conn in connections -*/
      /*- set idx = eval('[ idx for idx in range(len(conn.from_ends)) if i.name == conn.from_ends[idx].instance.name ]', {'i': i, 'conn': conn}) -*/
      /*- if idx -*/
          /*? j() ?*/ /*? c.name ?*/_/*? conn.from_ends[idx[0]].interface.name ?*/ \<Rightarrow> /*? conn.name ?*/
      /*- endif -*/
      /*- set idx = eval('[ idx for idx in range(len(conn.to_ends)) if i.name == conn.to_ends[idx].instance.name ]', {'i': i, 'conn': conn}) -*/
      /*- if idx -*/
          /*? j() ?*/ /*? c.name ?*/_/*? conn.to_ends[idx[0]].interface.name ?*/ \<Rightarrow> /*? conn.name ?*/
      /*- endif -*/
  /*- endfor -*/
  )"
(** TPP: condense = False *)

/*- endfor -*/

/*# Simulated component instance for each event connection. #*/
/*- for c in filter(lambda('x: x.type.from_type == \'Event\''), connections) -*/
definition
  /*? c.name ?*/\<^sub>e_instance :: "(channel, 'cs) comp"
where
  "/*? c.name ?*/\<^sub>e_instance \<equiv> /*? c.from_interface.type ?*/ (\<lambda>_. /*? c.name ?*/)"
/*- endfor -*/

/*# Simulated component instance for each dataport connection. #*/
/*- for c in filter(lambda('x: x.type.from_type == \'Dataport\''), connections) -*/
definition
  /*? c.name ?*/\<^sub>d_instance :: "(channel, 'cs) comp"
where
  "/*? c.name ?*/\<^sub>d_instance \<equiv> /*? c.from_interface.type ?*/\<^sub>d (\<lambda>_. /*? c.name ?*/)"
/*- endfor -*/

(* Global initial state *)
/*# Even though this is generated as a mapping to an option type it is actually
 ** full.
 #*/
(** TPP: condense = True *)
definition
  gs\<^sub>0 :: "(inst, channel, 'cs) global_state"
where
  /*- set p = isabelle_symbol('p') -*/
  /*- set s = isabelle_symbol() -*/
  "gs\<^sub>0 /*? p ?*/ \<equiv> case trusted /*? p ?*/ of Some /*? s ?*/ \<Rightarrow> Some /*? s ?*/ | _ \<Rightarrow> (case /*? p ?*/ of
  /*- set j = joiner('|') -*/
  /*- for i in instances -*/
      /*? j() ?*/ /*? i.name ?*/ \<Rightarrow> Some (/*? i.name ?*/_untrusted, Component init_component_state)
  /*- endfor -*/
  /*- for c in connections -*/
      /*- if c.type.from_type == 'Event' -*/
          /*? j() ?*/ /*? c.name ?*/\<^sub>e \<Rightarrow> Some (/*? c.name ?*/\<^sub>e_instance, init_event_state)
      /*- elif c.type.from_type == 'Dataport' -*/
          /*? j() ?*/ /*? c.name ?*/\<^sub>d \<Rightarrow> Some (/*? c.name ?*/\<^sub>d_instance, init_memory_state)
      /*- endif -*/
  /*- endfor -*/
  )"
(** TPP: condense = False *)

end

end
