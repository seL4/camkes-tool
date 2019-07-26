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

(* /*? macros.generated_file_notice() ?*/ *)

/*? macros.check_isabelle_outfile(
        '%s_Arch_Spec' % options.verification_base_name, outfile_name) ?*/

theory "/*? options.verification_base_name ?*/_Arch_Spec" imports
  "CamkesAdlSpec.Types_CAMKES"
  "CamkesAdlSpec.Library_CAMKES"
  "CamkesAdlSpec.Wellformed_CAMKES"
  "Lib.Qualify"
begin

(*
 * We restrict the scope of all names to a locale with the same name
 * as our theory. This ensures that entity names from the CAmkES
 * assembly won't overlap with names we use elsewhere.
 *)

locale /*? options.verification_base_name ?*/_Arch_Spec
begin

/*- macro camkes_type(type) -*/
    /*- if type == 'int' -*/
        Primitive (Numerical Integer)
    /*- elif type == 'unsigned int' -*/
        Primitive (Numerical UnsignedInteger)
    /*- elif type == 'real' -*/
        Primitive (Numerical Real)
    /*- elif type == 'char' -*/
        Primitive (Textual char)
    /*- elif type == 'character' -*/
        Primitive (Textual Character)
    /*- elif type == 'boolean' -*/
        Primitive (Numerical Boolean)
    /*- elif type == 'string' -*/
        Primitive (Textual String)
    /*- else -*/
        CType ''/*? type ?*/''
    /*- endif -*/
/*- endmacro -*/

/*- macro param_type(param) -*/
    /*- if param.array -*/
        Array (SizedArray
        /*- if type == 'int' -*/
            (Numerical Integer)
        /*- elif type == 'unsigned int' -*/
            (Numerical UnsignedInteger)
        /*- elif type == 'real' -*/
            (Numerical Real)
        /*- elif type == 'char' -*/
            (Textual char)
        /*- elif type == 'character' -*/
            (Textual Character)
        /*- elif type == 'boolean' -*/
            (Numerical Boolean)
        /*- else -*/
            /*? raise(TemplateError('unsupported type: array of %s' % param.type)) ?*/
        /*- endif -*/
    /*- else -*/
    /*- endif -*/
    /*? 'Array (SizedArray (' if param.array else '' ?*/
    /*? camkes_type(param.type) ?*/
    /*? '))' if param.array else '' ?*/
/*- endmacro -*/

/*- if hasattr(me, 'name') and me.name is not none -*/
    /*- set assembly = me.name -*/
/*- else -*/
    /*- set assembly = 'assembly\'' -*/
/*- endif -*/

/*- if hasattr(me.composition, 'name') and me.composition.name is not none -*/
    /*- set composition = me.composition.name -*/
/*- else -*/
    /*- set composition = 'composition\'' -*/
/*- endif -*/

/*- if me.configuration is not none and hasattr(me.configuration, 'name') and me.configuration.name is not none -*/
    /*- set configuration = me.configuration.name -*/
/*- else -*/
    /*- set configuration = 'configuration\'' -*/
/*- endif -*/

(* Connector types *)
/*- for i in uniq(map(lambda('x: x.type'), me.composition.connections)) -*/
definition
    /*? isabelle_connector(i.name) ?*/ :: connector
where[wellformed_CAMKES_simps]:
    "/*? isabelle_connector(i.name) ?*/ \<equiv> /*-
  if i.get_attribute('isabelle_connector_spec') -*//*? i.get_attribute('isabelle_connector_spec').default ?*//*-
  else -*/\<lparr>
        connector_type = /*? 'HardwareConnector' if i.from_hardware or i.to_hardware else 'NativeConnector' ?*/,
        connector_interface =
          /*- if i.from_type == 'Dataport' -*/
            DataportInterface,
          /*- elif i.from_type == 'Event' -*/
            EventInterface,
          /*- elif i.from_type == 'Procedure' -*/
            RPCInterface,
          /*- endif -*/
        connector_access = \<lparr>
            access_from_to   = undefined ''TODO /*? isabelle_connector(i.name) ?*/.access_from_to'',
            access_to_from   = undefined ''TODO /*? isabelle_connector(i.name) ?*/.access_to_from'',
            access_from_conn = undefined ''TODO /*? isabelle_connector(i.name) ?*/.access_from_conn'',
            access_to_conn   = undefined ''TODO /*? isabelle_connector(i.name) ?*/.access_to_conn''
        \<rparr> \<rparr>/*-
  endif -*/"
lemma[wellformed_CAMKES_simps]: "wellformed_connector /*? isabelle_connector(i.name) ?*/"
  by (auto simp: wellformed_CAMKES_simps /*? isabelle_connector(i.name) ?*/_def)
/*- endfor -*/

(* Procedure interfaces *)
/*- for i in uniq(map(lambda('x: x.type'), flatMap(lambda('x: x.type.uses + x.type.provides'), me.composition.instances))) -*/
definition
    /*? isabelle_procedure(i.name) ?*/ :: procedure
where[wellformed_CAMKES_simps]:
    "/*? isabelle_procedure(i.name) ?*/ \<equiv>
    /*- for m in i.methods -*/
        \<lparr> m_return_type =
        /*- if m.return_type -*/
            Some (/*? camkes_type(m.return_type) ?*/)
        /*- else -*/
            None
        /*- endif -*/
        , m_name = ''/*? m.name ?*/'',
        m_parameters =
        /*- for p in m.parameters -*/
            \<lparr> p_type = /*? param_type(p) ?*/,
            p_direction =
            /*- if p.direction in ['in', 'refin'] -*/
                InParameter
            /*- elif p.direction == 'out' -*/
                OutParameter
            /*- else -*/
                /*? assert(p.direction == 'inout') ?*/
                InOutParameter
            /*- endif -*/
            , p_name = ''/*? p.name ?*/'' \<rparr> #
        /*- endfor -*/
        [] \<rparr> #
    /*- endfor -*/
    []"

lemma wf_/*? isabelle_procedure(i.name) ?*/: "wellformed_procedure /*? isabelle_procedure(i.name) ?*/"
  by (simp add: wellformed_CAMKES_simps)
/*- endfor -*/

(* Event interfaces *)
/*- for index, i in enumerate(uniq(map(lambda('x: x.type'), flatMap(lambda('x: x.type.emits + x.type.consumes'), me.composition.instances)))) -*/
definition
    /*? isabelle_event(i) ?*/ :: event
where[wellformed_CAMKES_simps]:
    "/*? isabelle_event(i) ?*/ \<equiv> /*? index ?*/"

lemma wf_/*? isabelle_event(i) ?*/: "wellformed_event /*? isabelle_event(i) ?*/"
  by (simp add: wellformed_CAMKES_simps)
/*- endfor -*/

(* Dataport interfaces *)

/*- for i in uniq(map(lambda('x: x.type'), flatMap(lambda('x: x.type.dataports'), me.composition.instances))) -*/
definition
    /*? isabelle_dataport(i) ?*/ :: dataport
where[wellformed_CAMKES_simps]:
    "/*? isabelle_dataport(i) ?*/ \<equiv> Some ''/*? i ?*/''"

lemma wf_/*? isabelle_dataport(i) ?*/: "wellformed_dataport /*? isabelle_dataport(i) ?*/"
  by (simp add: wellformed_CAMKES_simps)
/*- endfor -*/

/*- for c in uniq(map(lambda('x: x.type'), me.composition.instances)) -*/
definition
    /*? isabelle_instance(c.name) ?*/ :: component
where[wellformed_CAMKES_simps]:
    "/*? isabelle_instance(c.name) ?*/ \<equiv> \<lparr>
        control =
        /*- if c.control -*/
            True
        /*- else -*/
            False
        /*- endif -*/
        ,
        hardware =
        /*- if c.hardware -*/
            True
        /*- else -*/
            False
        /*- endif -*/
        ,
        requires =
        /*- for i in c.uses -*//*-
                if c.interface_is_exported(i.name) -*/
            \<comment> \<open>Exported interface/*- endif -*/
            (''/*? i.name ?*/'', /*? isabelle_procedure(i.type.name) ?*/) #/*-
                if c.interface_is_exported(i.name) -*/
            \<close>/*- endif -*/
        /*- endfor -*/
        [],
        provides =
        /*- for i in c.provides -*//*-
                if c.interface_is_exported(i.name) -*/
            \<comment> \<open>Exported interface/*- endif -*/
            (''/*? i.name ?*/'', /*? isabelle_procedure(i.type.name) ?*/) #/*-
                if c.interface_is_exported(i.name) -*/
            \<close>/*- endif -*/
        /*- endfor -*/
        [],
        dataports =
        /*- for i in c.dataports -*//*-
                if c.interface_is_exported(i) -*/
            \<comment> \<open>Exported interface/*- endif -*/
            (''/*? i ?*/'', /*? isabelle_dataport(i.type) ?*/) #/*-
                if c.interface_is_exported(i) -*/
            \<close>/*- endif -*/
        /*- endfor -*/
        [],
        emits =
        /*- for i in c.emits -*//*-
                if c.interface_is_exported(i) -*/
            \<comment> \<open>Exported interface/*- endif -*/
            (''/*? i ?*/'', /*? isabelle_event(i.type) ?*/) #/*-
                if c.interface_is_exported(i) -*/
            \<close>/*- endif -*/
        /*- endfor -*/
        [],
        consumes =
        /*- for i in c.consumes -*//*-
                if c.interface_is_exported(i) -*/
            \<comment> \<open>Exported interface/*- endif -*/
            (''/*? i ?*/'', /*? isabelle_event(i.type) ?*/) #/*-
                if c.interface_is_exported(i) -*/
            \<close>/*- endif -*/
        /*- endfor -*/
        [],
        attributes =
        /*- for a in c.attributes -*/
            (''/*? a.name ?*/'', /*? camkes_type(a.type) ?*/) #
        /*- endfor -*/
        []
    \<rparr>"

lemma wf_/*? isabelle_instance(c.name) ?*/: "wellformed_component /*? isabelle_instance(c.name) ?*/"
  by (simp add: wellformed_CAMKES_simps)
/*- endfor -*/

/*- for i in me.composition.instances -*/
definition
    /*? isabelle_component(i.name) ?*/ :: component
where[wellformed_CAMKES_simps]:
    "/*? isabelle_component(i.name) ?*/ \<equiv> /*? isabelle_instance(i.type.name) ?*/"

lemma wf_/*? isabelle_component(i.name) ?*/: "wellformed_component /*? isabelle_component(i.name) ?*/"
  by (simp add: wellformed_CAMKES_simps)
/*- endfor -*/

/*- for c in me.composition.connections -*/
definition
    /*? isabelle_connection(c.name) ?*/ :: connection
where[wellformed_CAMKES_simps]:
    "/*? isabelle_connection(c.name) ?*/ \<equiv> \<lparr>
        conn_type = /*? isabelle_connector(c.type.name) ?*/,
        conn_from =
        /*- for i, from_end in enumerate(c.from_ends) -*/
          (''/*? from_end.instance.name ?*/'', ''/*? from_end.interface.name ?*/'') #
        /*- endfor -*/
          [],
        conn_to =
        /*- for i, to_end in enumerate(c.to_ends) -*/
          (''/*? to_end.instance.name ?*/'', ''/*? to_end.interface.name ?*/'') #
        /*- endfor -*/
          []
    \<rparr>"

lemma wf_/*? isabelle_connection(c.name) ?*/: "wellformed_connection /*? isabelle_connection(c.name) ?*/"
  by (simp add: wellformed_CAMKES_simps)
/*- endfor -*/

definition
    /*? composition ?*/ :: composition
where[wellformed_CAMKES_simps]:
    "/*? composition ?*/ \<equiv> \<lparr>
        components =
        /*- for c in me.composition.instances -*/
            (''/*? c.name ?*/'', /*? isabelle_component(c.name) ?*/) #
        /*- endfor -*/
        [],
        connections =
        /*- for c in me.composition.connections -*/
            (''/*? c.name ?*/'', /*? isabelle_connection(c.name) ?*/) #
        /*- endfor -*/
        []
    \<rparr>"

lemma wf_/*? composition ?*/: "wellformed_composition /*? composition ?*/"
  by (simp add: wellformed_CAMKES_simps)

definition
    /*? configuration ?*/ :: "configuration option"
where[wellformed_CAMKES_simps]:
    "/*? configuration ?*/ \<equiv>
    /*- if me.configuration -*/
        Some (
        /*- for s in me.configuration.settings -*/
            (''/*? s.instance ?*/'', ''/*? s.attribute ?*/'', ''/*? s.value ?*/'') #
        /*- endfor -*/
        [])
    /*- else -*/
        None
    /*- endif -*/
    "

lemma wf_/*? configuration ?*/:
/*- if me.configuration -*/
    "wellformed_configuration (the /*? configuration ?*/)"
    by (simp add: wellformed_CAMKES_simps)
/*- else -*/
    (* No configuration *)/*# If there is no configuration it is trivially wellformed. #*/
    "True"
    by simp
/*- endif -*/

definition
    /*? assembly ?*/ :: assembly
where[wellformed_CAMKES_simps]:
    "/*? assembly ?*/ \<equiv> \<lparr>
        composition = /*? composition ?*/,
        configuration = /*? configuration ?*/
    \<rparr>"

lemma wf_/*? assembly ?*/: "wellformed_assembly /*? assembly ?*/"
  by (simp add: wellformed_CAMKES_simps)

end

end
