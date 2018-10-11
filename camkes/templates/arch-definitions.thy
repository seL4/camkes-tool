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

theory "/*? macros.isabelle_theory_name(outfile_name) ?*/" imports
  "CamkesAdlSpec.Types_CAMKES"
  "CamkesAdlSpec.Library_CAMKES"
  "CamkesAdlSpec.Wellformed_CAMKES"
  "Lib.Qualify"
begin

(* /*? macros.generated_file_notice() ?*/ *)

(* We restrict the scope of all names to a locale with the same name
 * as our theory. This ensures that entity names from the CAmkES
 * assembly won't overlap with names we use elsewhere. *)

locale /*? macros.isabelle_theory_name(outfile_name) ?*/
qualify /*? macros.isabelle_theory_name(outfile_name) ?*/

/*- macro param_type(type) -*/
    /*- if type == 'int' -*/
        Primitive (Numerical Integer)
    /*- elif type == 'unsigned int' -*/
        Primitive (Numerical UnsignedInteger)
    /*- elif type in ['int8_t', 'int16_t', 'int32_t', 'int64_t', 'uint8_t', 'uint16_t', 'uint32_t', 'uint64_t', 'double', 'float', 'uintptr_t'] -*/
        /*# C-specific types #*/
        Primitive (Numerical /*? type ?*/)
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
        /*? raise(TemplateError('unsupported type')) ?*/
    /*- endif -*/
/*- endmacro -*/

/*- if me.name is not none -*/
    /*- set assembly = me.name -*/
/*- else -*/
    /*- set assembly = 'assembly\'' -*/
/*- endif -*/

/*- if me.composition.name is not none -*/
    /*- set composition = me.composition.name -*/
/*- else -*/
    /*- set composition = 'composition\'' -*/
/*- endif -*/

/*- if me.configuration is not none and me.configuration.name is not none -*/
    /*- set configuration = me.configuration.name -*/
/*- else -*/
    /*- set configuration = 'configuration\'' -*/
/*- endif -*/

(* Procedure interfaces *)
/*- for i in uniq(map(lambda('x: x.type'), flatMap(lambda('x: x.type.uses + x.type.provides'), me.composition.instances))) -*/
definition
    /*? i.name ?*/ :: procedure
where
    "/*? i.name ?*/ \<equiv>
    /*- for m in i.methods -*/
        \<lparr> m_return_type =
        /*- if m.return_type -*/
            Some (/*? param_type(m.return_type) ?*/)
        /*- else -*/
            None
        /*- endif -*/
        , m_name = ''/*? m.name ?*/'',
        m_parameters =
        /*- for p in m.parameters -*/
            \<lparr> p_type = /*? param_type(p.type) ?*/,
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

lemma wf_/*? i.name ?*/: "wellformed_procedure /*? i.name ?*/"
  by code_simp
/*- endfor -*/

(* Event interfaces *)
/*- for index, i in enumerate(uniq(map(lambda('x: x.type'), flatMap(lambda('x: x.type.emits + x.type.consumes'), me.composition.instances)))) -*/
definition
    /*? i ?*/ :: event
where
    "/*? i ?*/ \<equiv> /*? index ?*/"

lemma wf_/*? i ?*/: "wellformed_event /*? i ?*/"
  by code_simp
/*- endfor -*/

(* Dataport interfaces *)
/*- for i in uniq(map(lambda('x: x.type'), flatMap(lambda('x: x.type.dataports'), me.composition.instances))) -*/
definition
    /*? i ?*/ :: dataport
where
    "/*? i ?*/ \<equiv> Some ''/*? i ?*/''"

lemma wf_/*? i ?*/: "wellformed_dataport /*? i ?*/"
  by code_simp
/*- endfor -*/

/*- for c in uniq(map(lambda('x: x.type'), me.composition.instances)) -*/
definition
    /*? c.name ?*/ :: component
where
    "/*? c.name ?*/ \<equiv> \<lparr>
        control =
        /*- if c.control -*/
            True
        /*- else -*/
            False
        /*- endif -*/
        ,
        requires =
        /*- for i in c.uses -*/
            (''/*? i.name ?*/'', /*? i.type.name ?*/) #
        /*- endfor -*/
        [],
        provides =
        /*- for i in c.provides -*/
            (''/*? i.name ?*/'', /*? i.type.name ?*/) #
        /*- endfor -*/
        [],
        dataports =
        /*- for i in c.dataports -*/
            (''/*? i.name ?*/'', /*? i.type ?*/) #
        /*- endfor -*/
        [],
        emits =
        /*- for i in c.emits -*/
            (''/*? i.name ?*/'', /*? i.type ?*/) #
        /*- endfor -*/
        [],
        consumes =
        /*- for i in c.consumes -*/
            (''/*? i.name ?*/'', /*? i.type ?*/) #
        /*- endfor -*/
        [],
        attributes =
        /*- for a in c.attributes -*/
            (''/*? a.name ?*/'', /*? param_type(a.type) ?*/) #
        /*- endfor -*/
        []
    \<rparr>"

lemma wf_/*? c.name ?*/: "wellformed_component /*? c.name ?*/"
  by code_simp
/*- endfor -*/

/*- for i in me.composition.instances -*/
definition
    /*? i.name ?*/ :: component
where
    "/*? i.name ?*/ \<equiv> /*? i.type.name ?*/"

lemma wf_/*? i.name ?*/: "wellformed_component /*? i.name ?*/"
  by code_simp
/*- endfor -*/

/*- for c in me.composition.connections -*/
definition
    /*? c.name ?*/ :: connection
where
    "/*? c.name ?*/ \<equiv> \<lparr>
        conn_type = /*? c.type.name ?*/,
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

lemma wf_/*? c.name ?*/: "wellformed_connection /*? c.name ?*/"
  by code_simp
/*- endfor -*/

definition
    /*? composition ?*/ :: composition
where
    "/*? composition ?*/ \<equiv> \<lparr>
        components =
        /*- for c in me.composition.instances -*/
            (''/*? c.name ?*/'', /*? c.name ?*/) #
        /*- endfor -*/
        [],
        connections =
        /*- for c in me.composition.connections -*/
            (''/*? c.name ?*/'', /*? c.name ?*/) #
        /*- endfor -*/
        []
    \<rparr>"

lemma wf_/*? composition ?*/: "wellformed_composition /*? composition ?*/"
  by code_simp

definition
    /*? configuration ?*/ :: "configuration option"
where
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
    by code_simp
/*- else -*/
    /*# If there is no configuration it is trivially wellformed. #*/
    "True"
    by simp
/*- endif -*/

definition
    /*? assembly ?*/ :: assembly
where
    "/*? assembly ?*/ \<equiv> \<lparr>
        composition = /*? composition ?*/,
        configuration = /*? configuration ?*/
    \<rparr>"

lemma wf_/*? assembly ?*/: "wellformed_assembly /*? assembly ?*/"
  by code_simp

end_qualify

end
