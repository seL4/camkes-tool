#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

from camkes.ast import Event, Port, Procedure, Method, Attribute, \
    Parameter, Type, Reference, Direction, Include

'''IDL parsing rules. See accompanying docs for more information.'''

def p_idl(t):
    '''idl :
           | import_statement idl
           | procedure_decl idl
           | event_decl idl
           | port_decl idl
           | SEMI idl'''
    if len(t) == 1:
        t[0] = []
    elif t[1] == ';':
        assert len(t) == 3
        t[0] = t[2]
    else:
        assert len(t) == 3
        t[0] = [t[1]] + t[2]

# Event
def p_event_decl(t):
    '''event_decl : event ID EQUALS event_defn SEMI'''
    t[0] = t[4]
    assert isinstance(t[0], Event)
    t[0].name = t[2]
    t[0].filename = t.lexer.filename
    t[0].lineno = t.lexer.lineno
def p_event_defn(t):
    '''event_defn : NUMBER'''
    t[0] = Event(id=t[1], filename=t.lexer.filename, lineno=t.lexer.lineno)

# Dataport
def p_port_decl(t):
    '''port_decl : dataport port_defn ID'''
    t[0] = t[2]
    assert isinstance(t[0], Port)
    t[0].name = t[3]
    t[0].filename = t.lexer.filename
    t[0].lineno = t.lexer.lineno
def p_port_defn(t):
    '''port_defn : ID'''
    t[0] = Port(type=t[1], filename=t.lexer.filename, lineno=t.lexer.lineno)

# Procedure
def p_procedure_decl(t):
    '''procedure_decl : procedure_keyword ID procedure_block
                      | procedure_keyword procedure_block'''
    if len(t) == 4:
        t[0] = t[3]
        assert isinstance(t[0], Procedure)
        t[0].name = t[2]
    else:
        assert len(t) == 3
        t[0] = t[2]
        assert isinstance(t[0], Procedure)
    t[0].filename = t.lexer.filename
    t[0].lineno = t.lexer.lineno
def p_procedure_block(t):
    '''procedure_block : LBRACE procedure_defn RBRACE'''
    includes, methods, attributes = t[2]
    assert isinstance(methods, list)
    for i in methods: assert isinstance(i, Method)
    assert isinstance(attributes, list)
    for i in attributes: assert isinstance(i, Attribute)
    t[0] = Procedure(None, includes, methods, attributes, filename=t.lexer.filename, \
        lineno=t.lexer.lineno)
def p_procedure_defn(t):
    '''procedure_defn : method
                      | method procedure_defn
                      | attribute_defn
                      | attribute_defn procedure_defn
                      | include_statement
                      | include_statement procedure_defn'''
    includes = []
    methods = []
    attributes = []
    if isinstance(t[1], Method):
        methods.append(t[1])
    elif isinstance(t[1], Attribute):
        attributes.append(t[1])
    else:
        assert isinstance(t[1], Include)
        includes.append(t[1])
    if len(t) == 3:
        i, m, a = t[2]
        includes += i
        methods += m
        attributes += a
    t[0] = (includes, methods, attributes)

def p_procedure_keyword(t):
    '''procedure_keyword : procedure
                         | interface'''
    t[0] = t[1]

def p_method(t):
    '''method : void ID LPAREN parameter_list RPAREN SEMI
              | type ID LPAREN parameter_list RPAREN SEMI
              | ID ID LPAREN parameter_list RPAREN SEMI'''
    if t[1] == 'void':
        return_type = None
    elif isinstance(t[1], Type):
        return_type = t[1]
    else:
        return_type = Reference(t[1], Type, filename=t.lexer.filename,
            lineno=t.lexer.lineno)
    name = t[2]
    parameters = t[4]
    assert isinstance(parameters, list)
    for i in parameters: assert isinstance(i, Parameter)
    t[0] = Method(name, return_type, parameters, filename=t.lexer.filename, \
        lineno=t.lexer.lineno)

def p_parameter_list(t):
    '''parameter_list :
                      | void
                      | parameter continuing_parameter_list'''
    if len(t) in [1, 2]:
        t[0] = []
    else:
        assert len(t) == 3
        t[0] = [t[1]] + t[2]

def p_continuing_parameter_list(t):
    '''continuing_parameter_list : COMMA parameter continuing_parameter_list
                                 |'''
    if len(t) == 4:
        t[0] = [t[2]] + t[3]
    else:
        assert len(t) == 1
        t[0] = []

def p_attribute_defn(t):
    '''attribute_defn : type ID SEMI'''
    t[0] = Attribute(t[2], t[1], filename=t.lexer.filename, lineno=t.lexer.lineno)

def p_parameter(t):
    '''parameter : direction type ID
                 | direction type ID LSQUARE RSQUARE
                 | direction ID ID
                 | direction ID ID LSQUARE RSQUARE'''
    array = len(t) == 6
    if isinstance(t[2], Type):
        t[0] = Parameter(t[3], t[1], t[2], array)
    else:
        t[0] = Parameter(t[3], t[1], Reference(t[2], Type, \
            filename=t.lexer.filename, lineno=t.lexer.lineno), array)
    t[0].filename = t.lexer.filename
    t[0].lineno = t.lexer.lineno

def p_direction(t):
    '''direction : in
                 | inout
                 | out'''
    t[0] = Direction(t[1], filename=t.lexer.filename, lineno=t.lexer.lineno)

def p_type(t):
    '''type : int
            | integer
            | signed int
            | unsigned int
            | signed integer
            | unsigned integer
            | int8_t
            | int16_t
            | int32_t
            | int64_t
            | uint8_t
            | uint16_t
            | uint32_t
            | uint64_t
            | real
            | double
            | float
            | uintptr_t
            | char
            | character
            | bool
            | boolean
            | string'''
    t[0] = Type(' '.join(t[1:]), filename=t.lexer.filename, lineno=t.lexer.lineno)
