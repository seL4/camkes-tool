/*#
 *# Copyright 2014, NICTA
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(NICTA_BSD)
 #*/

theory /*? splitext(os.path.basename(options.outfile.name))[0] ?*/ imports
    Types_CAMKES
    Library_CAMKES
    Wellformed_CAMKES
begin

/*# Ignore the following line. It is intended to apply to the output of this
 *# template.
#*/
(* THIS FILE IS GENERATED. DO NOT EDIT.
 * It is expected to be hosted in l4v/camkes/adl-spec.
 *)

/*- macro param_type(type) -*/
    /*- if type.type == 'int' -*/
        Primitive (Numerical Integer)
    /*- elif type.type == 'unsigned int' -*/
        Primitive (Numerical UnsignedInteger)
    /*- elif type.type in ['int8_t', 'int16_t', 'int32_t', 'int64_t', 'uint8_t', 'uint16_t', 'uint32_t', 'uint64_t', 'double', 'float', 'uintptr_t'] -*/
        /*# C-specific types #*/
        Primitive (Numerical /*? type.type ?*/)
    /*- elif type.type == 'real' -*/
        Primitive (Numerical Real)
    /*- elif type.type == 'char' -*/
        Primitive (Textual char)
    /*- elif type.type == 'character' -*/
        Primitive (Textual Character)
    /*- elif type.type == 'boolean' -*/
        Primitive (Numerical Boolean)
    /*- elif type.type == 'string' -*/
        Primitive (Textual String)
    /*- else -*/
        /*? raise(NotImplementedError) ?*/
    /*- endif -*/
/*- endmacro -*/

/*- if me.name -*/
    /*- set assembly = me.name -*/
/*- else -*/
    /*- set assembly = 'assembly\'' -*/
/*- endif -*/

/*- if me.composition.name -*/
    /*- set composition = me.composition.name -*/
/*- else -*/
    /*- set composition = 'composition\'' -*/
/*- endif -*/

/*- if me.configuration and me.configuration.name -*/
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
  by eval
/*- endfor -*/

(* Event interfaces *)
/*- for i in uniq(map(lambda('x: x.type'), flatMap(lambda('x: x.type.emits + x.type.consumes'), me.composition.instances))) -*/
definition
    /*? i.name ?*/ :: event
where
    "/*? i.name ?*/ \<equiv> /*? i.id ?*/"

lemma wf_/*? i.name ?*/: "wellformed_event /*? i.name ?*/"
  by eval
/*- endfor -*/

(* Dataport interfaces *)
/*- for i in uniq(map(lambda('x: x.type'), flatMap(lambda('x: x.type.dataports'), me.composition.instances))) -*/
definition
    /*? i.name ?*/ :: dataport
where
    "/*? i.name ?*/ \<equiv>
    /*- if i.type -*/
        Some ''/*? i.type ?*/''
    /*- else -*/
        None
    /*- endif -*/
    "

lemma wf_/*? i.name ?*/: "wellformed_dataport /*? i.name ?*/"
  by eval
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
            (''/*? i.name ?*/'', /*? i.type.name ?*/) #
        /*- endfor -*/
        [],
        emits =
        /*- for i in c.emits -*/
            (''/*? i.name ?*/'', /*? i.type.name ?*/) #
        /*- endfor -*/
        [],
        consumes =
        /*- for i in c.consumes -*/
            (''/*? i.name ?*/'', /*? i.type.name ?*/) #
        /*- endfor -*/
        [],
        attributes =
        /*- for a in c.attributes -*/
            (''/*? a.name ?*/'', /*? param_type(a.type) ?*/) #
        /*- endfor -*/
        []
    \<rparr>"

lemma wf_/*? c.name ?*/: "wellformed_component /*? c.name ?*/"
  by eval
/*- endfor -*/

/*- for i in me.composition.instances -*/
definition
    /*? i.name ?*/ :: component
where
    "/*? i.name ?*/ \<equiv> /*? i.type.name ?*/"

lemma wf_/*? i.name ?*/: "wellformed_component /*? i.name ?*/"
  by eval
/*- endfor -*/

/*- for c in me.composition.connections -*/
definition
    /*? c.name ?*/ :: connection
where
    "/*? c.name ?*/ \<equiv> \<lparr>
        conn_type = /*? c.type.name ?*/,
        conn_from = (''/*? c.from_instance.name ?*/'', ''/*? c.from_interface.name ?*/''),
        conn_to = (''/*? c.to_instance.name ?*/'', ''/*? c.to_interface.name ?*/'')
    \<rparr>"

lemma wf_/*? c.name ?*/: "wellformed_connection /*? c.name ?*/"
  by eval
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
  by eval

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
    "wellformed_configuration the /*? configuration ?*/"
    by eval
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
  by eval

end
