#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''ADL-relevant parsing rules. See accompanying docs for more information.'''

from camkes.ast import Connector, Assembly, Composition, Configuration, \
    Instance, Component, Setting, Interface, Include, \
    Provides, Uses, Consumes, Dataport, Emits, Connection, Procedure, \
    Port, Event, Reference, Attribute, Mutex, Semaphore, Group

def p_adl(t):
    '''adl :
           | import_statement adl
           | assembly_decl adl
           | composition_decl adl
           | component_decl adl
           | connector_decl adl
           | configuration_decl adl
           | SEMI adl'''
    if len(t) == 1:
        t[0] = []
    elif t[1] == ';':
        assert len(t) == 3
        t[0] = t[2]
    else:
        assert len(t) == 3
        t[0] = [t[1]] + t[2]

# Connector
def p_connector_decl(t):
    '''connector_decl : connector ID connector_block
                      | connector connector_block'''
    if len(t) == 4:
        t[0] = t[3]
        assert isinstance(t[0], Connector)
        t[0].name = t[2]
    else:
        t[0] = t[2]
        assert isinstance(t[0], Connector)
    t[0].filename = t.lexer.filename
    t[0].lineno = t.lexer.lineno
def p_connector_ref(t):
    '''connector_ref : ID
                     | connector_block'''
    assert len(t) == 2
    if isinstance(t[1], Connector):
        t[0] = t[1]
    else:
        t[0] = Reference(t[1], Connector)
    t[0].filename = t.lexer.filename
    t[0].lineno = t.lexer.lineno
def p_connector_block(t):
    '''connector_block : LBRACE connector_defn RBRACE'''
    t[0] = t[2]
    assert isinstance(t[0], Connector)
    t[0].filename = t.lexer.filename
    t[0].lineno = t.lexer.lineno
def p_connector_defn(t):
    '''connector_defn : from connector_end_type ID SEMI to connector_end_type ID SEMI
                      | from connector_end_type ID template STRING SEMI to connector_end_type ID SEMI
                      | from connector_end_type ID SEMI to connector_end_type ID template STRING SEMI
                      | from connector_end_type ID template STRING SEMI to connector_end_type ID template STRING SEMI'''
    from_template = None
    to_template = None
    from_type = t[2]
    if len(t) == 9:
        to_type = t[6]
    elif len(t) == 11:
        if t[4] == 'template':
            from_template = t[5]
            to_type = t[8]
        else:
            to_type = t[6]
            to_template = t[9]
    else:
        assert len(t) == 13
        from_template = t[5]
        to_type = t[8]
        to_template = t[11]
    t[0] = Connector(name=None, from_type=from_type, to_type=to_type,
        from_template=from_template, to_template=to_template,
        filename=t.lexer.filename, lineno=t.lexer.lineno)

# Assembly
def p_assembly_decl(t):
    '''assembly_decl : assembly assembly_block
                     | assembly ID assembly_block'''
    if len(t) == 3:
        t[0] = t[2]
        assert isinstance(t[2], Assembly)
    else:
        assert len(t) == 4
        t[0] = t[3]
        assert isinstance(t[0], Assembly)
        t[0].name = t[2]
    t[0].filename = t.lexer.filename
    t[0].lineno = t.lexer.lineno
# NB: assembly_ref not required.
def p_assembly_block(t):
    '''assembly_block : LBRACE assembly_defn RBRACE'''
    t[0] = t[2]
    assert isinstance(t[0], Assembly)
    t[0].filename = t.lexer.filename
    t[0].lineno = t.lexer.lineno
def p_assembly_defn(t):
    '''assembly_defn : composition_sing configuration_sing
                     | composition_sing
                     | configuration_sing composition_sing'''
    if len(t) == 2:
        assert isinstance(t[1], Composition) or isinstance(t[1], Reference)
        t[0] = Assembly(composition=t[1])
    else:
        assert len(t) == 3
        if isinstance(t[1], Composition) or \
                (isinstance(t[1], Reference) and t[1].symbol_type == Composition):
            assert isinstance(t[2], Configuration) or isinstance(t[2], Reference)
            t[0] = Assembly(composition=t[1], \
                            configuration=t[2])
        else:
            assert isinstance(t[1], Configuration) or isinstance(t[1], Reference)
            assert isinstance(t[2], Composition) or isinstance(t[2], Reference)
            t[0] = Assembly(composition=t[2], \
                            configuration=t[1])
    t[0].filename = t.lexer.filename
    t[0].lineno = t.lexer.lineno

# Composition
def p_composition_sing(t):
    '''composition_sing : composition ID SEMI
                        | composition_decl'''
    if len(t) == 4:
        t[0] = Reference(t[2], Composition)
    else:
        assert len(t) == 2
        t[0] = t[1]
        assert isinstance(t[0], Composition)
    t[0].filename = t.lexer.filename
    t[0].lineno = t.lexer.lineno
def p_composition_decl(t):
    '''composition_decl : composition composition_block
                        | composition ID composition_block'''
    if len(t) == 3:
        t[0] = t[2]
        assert isinstance(t[0], Composition)
    else:
        assert len(t) == 4
        t[0] = t[3]
        assert isinstance(t[0], Composition)
        t[0].name = t[2]
    t[0].filename = t.lexer.filename
    t[0].lineno = t.lexer.lineno
def p_composition_block(t):
    '''composition_block : LBRACE composition_defn RBRACE'''
    instances, connections, groups = t[2]
    assert isinstance(instances, list)
    for i in instances: assert isinstance(i, Instance)
    assert isinstance(connections, list)
    for c in connections: assert isinstance(c, Connection)
    t[0] = Composition(instances=instances,
                       connections=connections,
                       groups=groups,
                       filename=t.lexer.filename,
                       lineno=t.lexer.lineno)
def p_composition_defn(t):
    '''composition_defn :
                        | instance_defn composition_defn
                        | connection_defn composition_defn
                        | group_decl composition_defn'''
    if len(t) == 1:
        t[0] = ([], [], [])
    else:
        assert len(t) == 3
        instances, connections, groups = t[2]
        assert isinstance(instances, list)
        for i in instances: assert isinstance(i, Instance)
        assert isinstance(connections, list)
        for c in connections: assert isinstance(c, Connection)
        if isinstance(t[1], Instance):
            t[0] = (instances + [t[1]], connections, groups)
        elif isinstance(t[1], Connection):
            t[0] = (instances, connections + [t[1]], groups)
        else:
            assert isinstance(t[1], Group)
            t[0] = (instances, connections, groups + [t[1]])

def p_group_decl(t):
    '''group_decl : group group_block
                  | group ID group_block'''
    if len(t) == 3:
        t[0] = t[2]
    else:
        t[0] = t[3]
        assert isinstance(t[0], Group)
        t[0].name = t[2]

def p_group_block(t):
    '''group_block : LBRACE group_defn RBRACE'''
    t[0] = Group(instances=t[2])

def p_group_defn(t):
    '''group_defn :
                  | instance_defn group_defn'''
    if len(t) == 1:
        t[0] = []
    else:
        t[0] = t[2] + [t[1]]

def p_instance_defn(t):
    '''instance_defn : component component_ref ID SEMI'''
    assert isinstance(t[2], Component) or isinstance(t[2], Reference)
    t[0] = Instance(type=t[2], name=t[3], filename=t.lexer.filename, \
        lineno=t.lexer.lineno)

def p_connection_defn(t):
    '''connection_defn : connection connector_ref ID LPAREN from ID DOT ID COMMA to ID DOT ID RPAREN SEMI'''
    connector = t[2]
    name = t[3]
    from_instance = Reference(t[6], Instance, filename=t.lexer.filename, \
        lineno=t.lexer.lineno)
    from_interface = Reference(t[8], Interface, \
        filename=t.lexer.filename, lineno=t.lexer.lineno)
    to_instance = Reference(t[11], Instance, filename=t.lexer.filename, \
        lineno=t.lexer.lineno)
    to_interface = Reference(t[13], Interface, \
        filename=t.lexer.filename, lineno=t.lexer.lineno)
    t[0] = Connection(connector, name, from_instance, from_interface, \
        to_instance, to_interface, filename=t.lexer.filename, \
        lineno=t.lexer.lineno)

# Configuration
def p_configuration_sing(t):
    '''configuration_sing : configuration ID SEMI
                          | configuration_decl'''
    if len(t) == 4:
        t[0] = Reference(t[2], Configuration)
    else:
        assert len(t) == 2
        t[0] = t[1]
        assert isinstance(t[0], Configuration)
    t[0].filename = t.lexer.filename
    t[0].lineno = t.lexer.lineno
def p_configuration_decl(t):
    '''configuration_decl : configuration ID configuration_block
                          | configuration configuration_block'''
    if len(t) == 4:
        t[0] = t[3]
        assert isinstance(t[0], Configuration)
        t[0].name = t[2]
    else:
        assert len(t) == 3
        t[0] = t[2]
        assert isinstance(t[0], Configuration)
    t[0].filename = t.lexer.filename
    t[0].lineno = t.lexer.lineno
def p_configuration_block(t):
    '''configuration_block : LBRACE configuration_defn RBRACE'''
    assert isinstance(t[2], list)
    for c in t[2]: assert isinstance(c, Setting)
    t[0] = Configuration(name=None, settings=t[2], filename=t.lexer.filename, \
        lineno=t.lexer.lineno)
def p_configuration_defn(t):
    '''configuration_defn :
                          | setting_defn configuration_defn'''
    if len(t) == 1:
        t[0] = []
    else:
        assert len(t) == 3
        assert isinstance(t[2], list)
        for c in t[2]: assert isinstance(c, Setting)
        t[0] = [t[1]] + t[2]

def p_setting_defn(t):
    '''setting_defn : ID DOT ID EQUALS ID SEMI
                    | ID DOT ID EQUALS NUMBER SEMI
                    | ID DOT ID EQUALS DECIMAL SEMI
                    | setting_defn_string'''
    if len(t) == 2:
        t[0] = t[1]
    else:
        assert len(t) == 7
        t[0] = Setting(t[1], t[3], t[5], filename=t.lexer.filename, \
            lineno=t.lexer.lineno)

def p_setting_defn_string(t):
    '''setting_defn_string : ID DOT ID EQUALS STRING SEMI'''
    # This rule is only necessary (in addition to p_setting_defn) because
    # otherwise a match involving a STRING would be indistinguishable from a
    # match involving an ID.
    t[0] = Setting(t[1], t[3], '"' + t[5] + '"', filename=t.lexer.filename, \
        lineno=t.lexer.lineno)

# Component
def p_component_decl(t):
    '''component_decl : component ID component_block
                      | component component_block'''
    if len(t) == 4:
        t[0] = t[3]
        assert isinstance(t[0], Component)
        t[0].name = t[2]
    else:
        assert len(t) == 3
        t[0] = t[2]
        assert isinstance(t[0], Component)
    t[0].filename = t.lexer.filename
    t[0].lineno = t.lexer.lineno
def p_component_ref(t):
    '''component_ref : ID
                     | component_block'''
    if isinstance(t[1], Component):
        t[0] = t[1]
    else:
        t[0] = Reference(t[1], Component)
    t[0].filename = t.lexer.filename
    t[0].lineno = t.lexer.lineno
def p_component_block(t):
    '''component_block : LBRACE component_defn RBRACE'''
    includes, control, hardware, provides, uses, emits, consumes, dataports, \
        attributes, mutexes, semaphores = t[2]
    assert isinstance(control, bool)
    assert isinstance(hardware, bool)
    assert isinstance(provides, list)
    for p in provides: assert isinstance(p, Provides)
    assert isinstance(uses, list)
    for u in uses: assert isinstance(u, Uses)
    assert isinstance(consumes, list)
    for c in consumes: assert isinstance(c, Consumes)
    assert isinstance(dataports, list)
    for d in dataports: assert isinstance(d, Dataport)
    t[0] = Component(None, includes, control, hardware, provides, uses, emits, \
        consumes, dataports, attributes, mutexes, semaphores, \
        filename=t.lexer.filename, lineno=t.lexer.lineno)
def p_component_defn(t):
    '''component_defn :
                      | include_statement component_defn
                      | control SEMI component_defn
                      | hardware SEMI component_defn
                      | provides_statement component_defn
                      | uses_statement component_defn
                      | emits_statement component_defn
                      | consumes_statement component_defn
                      | dataport_statement component_defn
                      | attribute_statement component_defn
                      | mutex_statement component_defn
                      | semaphore_statement component_defn'''
    if len(t) == 1:
        t[0] = ([], False, False, [], [], [], [], [], [], [], [])
    elif len(t) == 4:
        includes, control, hardware, provides, uses, emits, consumes, \
            dataports, attributes, mutexes, semaphores = t[3]
        if t[1] == 'control':
            t[0] = includes, True, False, provides, uses, emits, consumes, \
                dataports, attributes, mutexes, semaphores
        else:
            assert t[1] == 'hardware'
            t[0] = includes, False, True, provides, uses, emits, consumes, \
                dataports, attributes, mutexes, semaphores
    else:
        assert len(t) == 3
        includes, control, hardware, provides, uses, emits, consumes, \
            dataports, attributes, mutexes, semaphores = t[2]
        if isinstance(t[1], Include):
            includes.append(t[1])
        elif isinstance(t[1], Provides):
            provides.append(t[1])
        elif isinstance(t[1], Uses):
            uses.append(t[1])
        elif isinstance(t[1], Emits):
            emits.append(t[1])
        elif isinstance(t[1], Consumes):
            consumes.append(t[1])
        elif isinstance(t[1], Dataport):
            dataports.append(t[1])
        elif isinstance(t[1], Attribute):
            attributes.append(t[1])
        elif isinstance(t[1], Mutex):
            mutexes.append(t[1])
        else:
            assert isinstance(t[1], Semaphore)
            semaphores.append(t[1])
        t[0] = includes, control, hardware, provides, uses, emits, consumes, \
            dataports, attributes, mutexes, semaphores

def p_provides_statement(t):
    '''provides_statement : provides ID ID SEMI'''
    t[0] = Provides(Reference(t[2], Procedure), t[3], \
        filename=t.lexer.filename, lineno=t.lexer.lineno)

def p_uses_statement(t):
    '''uses_statement : uses ID ID SEMI
                      | maybe uses ID ID SEMI'''
    if len(t) == 5:
        t[0] = Uses(Reference(t[2], Procedure), t[3])
    else:
        assert len(t) == 6
        t[0] = Uses(Reference(t[3], Procedure), t[4], optional=True)
    t[0].filename = t.lexer.filename
    t[0].lineno = t.lexer.lineno

def p_emits_statement(t):
    '''emits_statement : emits ID ID SEMI'''
    t[0] = Emits(Reference(t[2], Event), t[3], filename=t.lexer.filename, \
        lineno=t.lexer.lineno)

def p_consumes_statement(t):
    '''consumes_statement : consumes ID ID SEMI
                          | maybe consumes ID ID SEMI'''
    if len(t) == 5:
        t[0] = Consumes(Reference(t[2], Event), t[3])
    else:
        assert len(t) == 6
        t[0] = Consumes(Reference(t[3], Event), t[4], optional=True)
    t[0].filename = t.lexer.filename
    t[0].lineno = t.lexer.lineno

def p_dataport_statement(t):
    '''dataport_statement : dataport ID ID SEMI
                          | maybe dataport ID ID SEMI'''
    if len(t) == 5:
        t[0] = Dataport(Reference(t[2], Port), t[3])
    else:
        assert len(t) == 6
        t[0] = Dataport(Reference(t[3], Port), t[4], optional=True)
    t[0].filename = t.lexer.filename
    t[0].lineno = t.lexer.lineno

def p_attribute_statement(t):
    '''attribute_statement : attribute type ID SEMI'''
    t[0] = Attribute(t[2], t[3], filename=t.lexer.filename, \
        lineno=t.lexer.lineno)

def p_mutex_statement(t):
    '''mutex_statement : has mutex ID SEMI'''
    t[0] = Mutex(t[3], filename=t.lexer.filename, lineno=t.lexer.lineno)

def p_semaphore_statement(t):
    '''semaphore_statement : has semaphore ID SEMI'''
    t[0] = Semaphore(t[3], filename=t.lexer.filename, lineno=t.lexer.lineno)

def p_connector_end_type(t):
    '''connector_end_type : Procedure
                          | Event
                          | Dataport
                          | Interface'''
    t[0] = t[1]
