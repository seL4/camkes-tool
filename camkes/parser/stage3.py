#!/usr/bin/env python
# -*- coding: utf-8 -*-

#
# Copyright 2017, Data61
# Commonwealth Scientific and Industrial Research Organisation (CSIRO)
# ABN 41 687 119 230.
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(DATA61_BSD)
#

'''
Stage 3 parser. The following parser is designed to accept a stage 2 parser,
whose output it consumes. A stage 3 parser makes the following transformation:

    augmented_ast ⇒ lifted_ast
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

from camkes.ast import Assembly, Attribute, AttributeReference, Component, \
    Composition, Configuration, Connection, ConnectionEnd, Connector, \
    Consumes, Dataport, Emits, Export, Group, Include, Instance, Interface, \
    LiftedAST, Method, Mutex, normalise_type, Parameter, Procedure, Provides, \
    Reference, Semaphore, BinarySemaphore, Setting, SourceLocation, Uses, Struct
from .base import Parser
from .exception import ParseError
import numbers, plyplus, re, six

class Parse3(Parser):
    def __init__(self, parse2, debug=False):
        self.parse2 = parse2
        self.debug = debug

    def parse_file(self, filename):
        ast_augmented, read = self.parse2.parse_file(filename)
        ast_lifted = lift(ast_augmented, self.debug)
        return ast_lifted, read

    def parse_string(self, content):
        ast_augmented, read = self.parse2.parse_string(content)
        ast_lifted = lift(ast_augmented, self.debug)
        return ast_lifted, read

def pairwise(xs):
    it = iter(xs)
    return zip(it, it)

# Items in the plyplus AST from which we cannot learn anything further by
# looking inside. Basically things who's children cannot be lifted.
DONT_DESCEND = frozenset([
    'angle_string',
    'char',
    'connector_end_type',
    'control',
    'direction',
    'from',
    'hardware',
    'id',
    'include', # Marked DONT_DESCEND because we need to discriminate between
               # double quoted strings and angle bracketed strings.
    'maybe',
    'quoted_string',
    'signed_char',
    'signed_int',
    'to',
    'unsigned_char',
    'unsigned_int',
])

# Items that we should never try and lift. Treat lifting as a no-op and assume
# their parent will handle the remaining STree.
DONT_LIFT = frozenset([
    'add',
    'band',
    'bor',
    'div',
    'eq',
    'gt',
    'gte',
    'land',
    'ls',
    'lt',
    'lte',
    'lor',
    'mod',
    'mul',
    'neq',
    'pow',
    'rs',
    'sub',
    'xor',
])

def lift(ast_augmented, debug=False):
    items = [lift_raw(x, name, source, debug) for source, name, x in ast_augmented]
    return LiftedAST(items)

def lift_raw(term, filename=None, source=None, debug=False):
    if not plyplus.is_stree(term):
        return six.text_type(term)

    if term.head in DONT_LIFT:
        return term

    if term.head in DONT_DESCEND:
        children = term.tail
    else:
        children = [lift_raw(t, filename, source, debug) for t in term.tail]

    location = SourceLocation(filename, term, source)

    try:
        lifter = LIFT[term.head]
    except KeyError:
        raise Exception('no lifter found for %s' % term.head)

    try:
        return lifter(location, *children)
    except (ParseError, AssertionError):
        raise
    except Exception as e:
        if debug:
            raise
        # If some other error occurred, attach filename and line number
        # information to it.
        raise ParseError(e, location)

def strip_quotes(s):
    if isinstance(s, six.string_types):
        assert s[0] == s[-1] == '"', 'unquoted string used where ' \
            'quoted string expected (bug in stage 1 parser?)'
        return s[1:-1]
    else:
        return s

def _lift_method_array_parameter(location, scalar_parameter):
    return Parameter(scalar_parameter.name, scalar_parameter.direction,
        scalar_parameter.type, True, location)

def _lift_attribute_array_parameter(location, scalar_parameter):
    return Attribute(scalar_parameter.type, scalar_parameter.name, True, default= None, location=location)

def _lift_assembly_decl(location, *args):
    if len(args) == 2:
        id, assembly_defn = args
    else:
        id = None
        assembly_defn = args[0]
    return Assembly(id, composition=assembly_defn.composition,
        configuration=assembly_defn.configuration, location=location)

def _lift_assembly_defn(location, *args):
    compositions = [x for x in args if isinstance(x, Composition)]
    assert len(compositions) == 1
    composition = compositions[0]
    configurations = [x for x in args if isinstance(x, Configuration)]
    assert len(configurations) <= 1
    configuration = configurations[0] if len(configurations) == 1 else None
    return Assembly(composition=composition, configuration=configuration,
        location=location)

def _lift_attribute(location, attribute_param, default=None):
    if isinstance(default, six.string_types):
        assert default[0] == default[-1] == '"', 'unquoted string used as ' \
            'attribute default value (bug in stage 1 parser?)'
        default = default[1:-1] # Strip quotes
    return Attribute(attribute_param.type, attribute_param.name, attribute_param.array, default, location)

def _lift_attribute_reference(location, *ids):
    return AttributeReference('.'.join(ids), location)

def _lift_boolean_literal(location, text):
    if text in ('True', 'true'):
        return 1
    return 0

def _lift_bitwise_not(location, op):
    return -1 - op

def _lift_char(location, *_):
    return 'char'

def _lift_struct_decl(location, id, struct_defn):
    return Struct(id, attributes=struct_defn.attributes, location=location)

def _lift_struct_defn(location, *args):
    assert len(args) > 0
    return Struct(attributes=args, location=location)

def _lift_struct_ref(location, arg):
    if isinstance(arg, Struct):
        return arg
    assert isinstance(arg, Reference)
    return Reference(arg.name, Struct, location)

def _lift_component_decl(location, *args):
    if len(args) == 1:
        return args[0]
    id, component_defn = args
    return Component(id, includes=component_defn.includes,
        control=component_defn.control, hardware=component_defn.hardware,
        provides=component_defn.provides, uses=component_defn.uses,
        emits=component_defn.emits, consumes=component_defn.consumes,
        dataports=component_defn.dataports,
        attributes=component_defn.attributes, mutexes=component_defn.mutexes,
        semaphores=component_defn.semaphores,
        binary_semaphores=component_defn.binary_semaphores,
        composition=component_defn.composition,
        configuration=component_defn.configuration, location=location)

def _lift_component_defn(location, *args):
    compositions = [x for x in args if isinstance(x, Composition)]
    assert len(compositions) <= 1
    composition = compositions[0] if len(compositions) == 1 else None
    configurations = [x for x in args if isinstance(x, Configuration)]
    assert len(configurations) <= 1
    configuration = configurations[0] if len(configurations) == 1 else None
    return Component(includes=[x for x in args if isinstance(x, Include)],
                     control='control' in args,
                     hardware='hardware' in args,
                     provides=[x for x in args if isinstance(x, Provides)],
                     uses=[x for x in args if isinstance(x, Uses)],
                     emits=[x for x in args if isinstance(x, Emits)],
                     consumes=[x for x in args if isinstance(x, Consumes)],
                     dataports=[x for x in args if isinstance(x, Dataport)],
                     attributes=[x for x in args if isinstance(x, Attribute)],
                     mutexes=[x for x in args if isinstance(x, Mutex)],
                     semaphores=[x for x in args if isinstance(x, Semaphore)],
                     binary_semaphores=[x for x in args if isinstance(x, BinarySemaphore)],
                     composition=composition, configuration=configuration,
                     location=location)

def _lift_component_ref(location, arg):
    if isinstance(arg, Component):
        return arg
    assert isinstance(arg, Reference)
    return Reference(arg.name, Component, location)

def _lift_composition_decl(location, *args):
    if len(args) == 2:
        id, composition_defn = args
        return Composition(id, instances=composition_defn.instances,
            connections=composition_defn.connections,
            groups=composition_defn.groups, exports=composition_defn.exports,
            location=location)
    composition_defn = args[0]
    return Composition(instances=composition_defn.instances,
        connections=composition_defn.connections,
        groups=composition_defn.groups, exports=composition_defn.exports,
        location=location)

def _lift_composition_defn(location, *args):
    return Composition(instances=[x for x in args if isinstance(x, Instance)],
                       connections=[x for x in args if isinstance(x, Connection)],
                       groups=[x for x in args if isinstance(x, Group)],
                       exports=[x for x in args if isinstance(x, Export)],
                       location=location)

def _lift_composition_sing(location, arg):
    if isinstance(arg, Composition):
        return arg
    assert isinstance(arg, Reference)
    return Reference(arg.name, Composition, location)

def _lift_configuration_decl(location, *args):
    if len(args) == 2:
        id, configuration_defn = args
        return Configuration(id, configuration_defn.settings)
    configuration_defn = args[0]
    return configuration_defn

def _lift_configuration_defn(location, *settings):
    return Configuration(settings=list(settings), location=location)

def _lift_configuration_sing(location, arg):
    if isinstance(arg, Configuration):
        return arg
    assert isinstance(arg, Reference)
    return Reference(arg.name, Configuration, location)

def _lift_connection_defn(location, connector_ref, id, *ends):
    return Connection(connector_ref, id, [e for e in ends if e.end == 'from'],
        [e for e in ends if e.end == 'to'], location)

def _lift_connection_end(location, end, ref):
    if len(ref.name) > 1:
        instance = Reference(ref.name[:-1], Instance, ref.location)
    else:
        instance = None
    return ConnectionEnd(end, instance, Reference(ref.name, Interface,
        ref.location), location)

def _lift_connector_decl(location, *args):
    if len(args) == 1:
        return args[0]
    id, connector_defn = args
    if connector_defn.from_multiple:
        from_type = '%ss' % connector_defn.from_type
    else:
        from_type = connector_defn.from_type
    if connector_defn.to_multiple:
        to_type = '%ss' % connector_defn.to_type
    else:
        to_type = connector_defn.to_type

    return Connector(id, from_type, to_type, connector_defn.from_template,
        connector_defn.to_template, connector_defn.from_threads,
        connector_defn.to_threads, connector_defn.from_hardware,
        connector_defn.to_hardware, location=location)

def _lift_connector_defn(location, *args):

    # Defaults
    from_template = None
    to_template = None
    from_threads = 1
    to_threads = 1
    from_hardware = False
    to_hardware = False

    def thread_count(value):
        '''
        Validate a number of threads for a connector end.
        '''
        try:
            v = int(value)
            if v < 0 or v != value:
                raise ValueError
        except ValueError:
            raise ParseError('illegal thread value \'%s\'' % value, location)
        return v

    if args[0] == 'hardware':
        from_hardware = True
        args = args[1:]

    from_type, args = args[0], args[1:]

    # The loops in this function are a little ad hoc, but are justified by
    # 'template' arguments appearing as raw strings and 'threads' arguments as
    # raw numbers. The motivation is to allow these two arguments to appear in
    # either order. See the grammar for more details.

    while isinstance(args[0], numbers.Number) or args[0].startswith('"'):
        if isinstance(args[0], numbers.Number):
            from_threads, args = thread_count(args[0]), args[1:]
        else:
            assert args[0].startswith('"')
            from_template, args = args[0][1:-1], args[1:]

    if args[0] == 'hardware':
        to_hardware = True
        args = args[1:]

    to_type, args = args[0], args[1:]

    while len(args) > 0:
        if isinstance(args[0], numbers.Number):
            to_threads, args= thread_count(args[0]), args[1:]
        else:
            assert args[0].startswith('"'), 'unexpected child of ' \
                'connector definition (bug in grammar?)'
            to_template, args = args[0][1:-1], args[1:]

    return Connector(from_type=from_type, to_type=to_type,
        from_template=from_template, to_template=to_template,
        from_threads=from_threads, to_threads=to_threads,
        from_hardware=from_hardware, to_hardware=to_hardware,
        location=location)

def _lift_connector_ref(location, arg):
    if isinstance(arg, Connector):
        return arg
    assert isinstance(arg, Reference)
    return Reference(arg.name, Connector, location)

def _lift_control(location, *_):
    return 'control'

def _lift_consumes(location, *args):
    if len(args) == 3:
        optional = True
        _, type, name = args
    else:
        optional = False
        type, name = args
    return Consumes(type, name, optional, location)

def _lift_dataport(location, *args):
    if len(args) == 3:
        optional = True
        _, type, name = args
    else:
        optional = False
        type, name = args
    return Dataport(type, name, optional, location)

def _lift_dataport_type(location, arg):
    if isinstance(arg, plyplus.plyplus.TokValue):
        return six.text_type(arg)
    assert isinstance(arg, numbers.Number), 'unexpected child of ' \
        'dataport_type (bug in grammar?)'
    if int(arg) != arg or arg <= 0:
        raise ParseError('illegal value for dataport size', location)
    return 'Buf(%d)' % int(arg)

def _lift_dict(location, *args):
    return {strip_quotes(k): strip_quotes(v) for k, v in pairwise(args)}

def _lift_emits(location, id, id2):
    return Emits(id, id2, location)

def _lift_export(location, ref1, ref2):
    assert isinstance(ref1, Reference)
    assert isinstance(ref2, Reference)
    if len(ref1.name) < 2:
        raise ParseError('illegal source in export statement (these must be '
            'qualified references like "foo.bar")', ref1.location)
    return Export(Reference(ref1.name[:-1], Instance, ref1.location),
        Reference(ref1.name, Interface, ref1.location),
        Reference(ref2.name, Interface, ref2.location), location)

def _lift_from(location, *_):
    return 'from'

def _lift_group_decl(location, *args):
    if len(args) == 2:
        id, group_defn = args
        return Group(id, group_defn.instances, location)
    group_defn = args[0]
    return Group(instances=group_defn.instances, location=location)

def _lift_group_defn(location, *instances):
    return Group(instances=list(instances), location=location)

def _lift_include(location, source):
    if source.head == 'multi_string':
        return Include(''.join(str(x.tail[0][1:-1]) for x in source.tail), True,
            location)
    assert source.head == 'angle_string', '%s inside an include statement ' \
        'where only a multi_string or angle_string are expected (mismatch ' \
        'between grammar and stage 3 parser?)' % source.head
    return Include(source.tail[0][1:-1], False, location)

def _lift_hardware(location, *_):
    return 'hardware'

def _lift_instance_defn(location, component_ref, id):
    return Instance(component_ref, id, location)

def _lift_list(location, *args):
    return [strip_quotes(x) for x in args]

def _lift_logical_not(location, op):
    return int(not op)

def _lift_method_decl(location, *args):
    if len(args) >= 2 and isinstance(args[1], six.string_types):
        return_type, args = args[0], args[1:]
        if isinstance(return_type, Reference):
            if len(return_type.name) != 1:
                raise ParseError("type: \"%s\" is not a valid type" % return_type.name, location)
            return_type = normalise_type(return_type.name[0]) # dont want references
    else:
        return_type = None # void
    id = args[0]
    return Method(id, return_type, list(args[1:]), location)

def _lift_multi_string(location, *strings):
    assert len(strings) >= 1, 'multi_string without any contained ' \
        'quoted_strings (bug in base grammar?)'
    return '"%s"' % ''.join(x[1:-1] for x in strings)

def _lift_mutex(location, id):
    return Mutex(id, location)

def _lift_number(location, text):
    if '.' in text:
        return float(text)
    return int(text, 0)

def _lift_numeric_expr(location, *ops):
    '''
    Lift a (possibly binary) numeric expression. This is not actually called
    directly as a lifting function, but used by the precedence lifters below.
    '''
    assert len(ops) % 2 == 1
    acc = ops[0]
    for operator, op in pairwise(ops[1:]):
        try:
            if operator.head == 'add':
                acc += op
            elif operator.head == 'band':
                acc &= op
            elif operator.head == 'bor':
                acc |= op
            elif operator.head == 'div':
                # If either operand is a float or similar, perform floating
                # point division. Otherwise floor the result.
                if not isinstance(acc, numbers.Integral) or \
                        not isinstance(op, numbers.Integral):
                    acc /= op
                else:
                    acc //= op
            elif operator.head == 'eq':
                acc = int(acc == op)
            elif operator.head == 'gt':
                acc = int(acc > op)
            elif operator.head == 'gte':
                acc = int(acc >= op)
            elif operator.head == 'land':
                acc = int(acc and op)
            elif operator.head == 'lor':
                acc = int(acc or op)
            elif operator.head == 'ls':
                acc <<= op
            elif operator.head == 'lt':
                acc = int(acc < op)
            elif operator.head == 'lte':
                acc = int(acc <= op)
            elif operator.head == 'mod':
                acc %= op
            elif operator.head == 'mul':
                acc *= op
            elif operator.head == 'neq':
                acc = int(acc != op)
            elif operator.head == 'pow':
                acc **= op
            elif operator.head == 'rs':
                acc >>= op
            elif operator.head == 'sub':
                acc -= op
            elif operator.head == 'xor':
                acc ^= op
            else:
                assert False, 'unexpected operator in numeric expression'
        except (ArithmeticError, TypeError, ValueError) as e:
            raise ParseError(e, location)
    return acc

def _lift_precedence11(location, *args):
    '''
    The ternary conditional.
    '''
    if len(args) == 1:
        # No ternary conditional. We just fall through to precedence10. See the
        # grammar for details.
        return args[0]
    else:
        assert len(args) == 3, 'unexpected number of atoms (%d) in ternary ' \
            'conditional (bug in stage 3 parser?)' % len(args)

        # The last parameter if the leading parameter is false...
        if args[0] == 0:
            return args[2]

        # ...otherwise the second parameter.
        return args[1]

def _lift_procedure_decl(location, *args):
    assert len(args) in (1, 2)
    if len(args) == 2:
        id, procedure_defn = args
        return Procedure(id, procedure_defn.includes, procedure_defn.methods,
            procedure_defn.attributes, location)
    return args[0]

def _lift_procedure_defn(location, *args):
    return Procedure(includes=[x for x in args if isinstance(x, Include)],
                     methods=[x for x in args if isinstance(x, Method)],
                     attributes=[x for x in args if isinstance(x, Attribute)],
                     location=location)

def _lift_provides(location, ref, id2):
    return Provides(Reference(ref.name, Procedure, ref.location), id2, location)

def _lift_reference(location, *ids):
    return Reference(list(ids), None, location)

def _lift_method_scalar_parameter(location, *args):
    if len(args) == 2:
        # Default the direction to 'in' if not specified.
        direction = 'in'
        type, id = args
    else:
        assert len(args) == 3
        direction, type, id = args
    if isinstance(type, Reference):
        if len(type.name) != 1:
            raise ParseError("type: \"%s\" is not a valid type" % type.name, location)
        type = normalise_type(type.name[0])
    return Parameter(id, direction, type, location=location)

def _lift_attribute_scalar_parameter(location, *args):
    assert len(args) == 2
    type, name = args
    assert(isinstance(type, (six.string_types, Reference, Struct)))
    if isinstance(type, six.string_types):
        # do not allow `struct blah` in attributes
        if type.startswith("struct "):
            raise ParseError("type: \"%s\" is not a valid type" % type, location)
    return Attribute(type, name, array=False, default= None, location=location)

def _lift_semaphore(location, id):
    return Semaphore(id, location)

def _lift_binary_semaphore(location, id):
    return BinarySemaphore(id, location)

def _lift_setting(location, id, id2, item):
    item = strip_quotes(item)
    return Setting(id, id2, item, location)

def _lift_signed_char(location, *_):
    return 'signed char'

def _lift_signed_int(location, *_):
    return 'int'

def _lift_struct_type(location, id):
    return 'struct %s' % id

def _lift_to(location, *_):
    return 'to'

def _lift_type(location, type_name):
    if isinstance(type_name, Reference):
        return type_name
    else:
        return normalise_type(type_name)

def _lift_unary_minus(location, op):
    return -op

def _lift_unsigned_char(location, *_):
    return 'unsigned char'

def _lift_unsigned_int(location, *_):
    return 'unsigned int'

def _lift_uses(location, *args):
    if len(args) == 3:
        optional = True
        _, type, name = args
    else:
        optional = False
        type, name = args
    return Uses(Reference(type.name, Procedure, type.location), name, optional, location)

def _collapse(location, content):
    return content

# Function dispatch table for abstracting plyplus STrees into native AST
# objects.
LIFT = {
    'angle_string':_collapse,
    'assembly_decl':_lift_assembly_decl,
    'assembly_defn':_lift_assembly_defn,
    'attribute_decl':_lift_attribute,
    'attribute_array_parameter':_lift_attribute_array_parameter,
    'attribute_reference':_lift_attribute_reference,
    'attribute_scalar_parameter': _lift_attribute_scalar_parameter,
    'boolean_literal':_lift_boolean_literal,
    'bitwise_not':_lift_bitwise_not,
    'char':_lift_char,
    'component_decl':_lift_component_decl,
    'component_defn':_lift_component_defn,
    'component_ref':_lift_component_ref,
    'composition_decl':_lift_composition_decl,
    'composition_defn':_lift_composition_defn,
    'composition_sing':_lift_composition_sing,
    'configuration_decl':_lift_configuration_decl,
    'configuration_defn':_lift_configuration_defn,
    'configuration_sing':_lift_configuration_sing,
    'connection_defn':_lift_connection_defn,
    'connection_end':_lift_connection_end,
    'connector_decl':_lift_connector_decl,
    'connector_defn':_lift_connector_defn,
    'connector_end_type':_collapse,
    'connector_ref':_lift_connector_ref,
    'consumes':_lift_consumes,
    'control':_lift_control,
    'dataport':_lift_dataport,
    'dataport_type':_lift_dataport_type,
    'dict':_lift_dict,
    'direction':_collapse,
    'emits':_lift_emits,
    'export':_lift_export,
    'from':_lift_from,
    'group_decl':_lift_group_decl,
    'group_defn':_lift_group_defn,
    'hardware':_lift_hardware,
    'hardware_bare':_collapse,
    'id':_collapse,
    'include':_lift_include,
    'instance_defn':_lift_instance_defn,
    'list':_lift_list,
    'logical_not':_lift_logical_not,
    'maybe':_collapse,
    'method_array_parameter':_lift_method_array_parameter,
    'method_decl':_lift_method_decl,
    'method_scalar_parameter':_lift_method_scalar_parameter,
    'multi_string':_lift_multi_string,
    'mutex':_lift_mutex,
    'number':_lift_number,
    'precedence1':_lift_numeric_expr,
    'precedence2':_lift_numeric_expr,
    'precedence3':_lift_numeric_expr,
    'precedence4':_lift_numeric_expr,
    'precedence5':_lift_numeric_expr,
    'precedence6':_lift_numeric_expr,
    'precedence7':_lift_numeric_expr,
    'precedence8':_lift_numeric_expr,
    'precedence9':_lift_numeric_expr,
    'precedence10':_lift_numeric_expr,
    'precedence11':_lift_precedence11,
    'procedure_decl':_lift_procedure_decl,
    'procedure_defn':_lift_procedure_defn,
    'provides':_lift_provides,
    'quoted_string':_collapse,
    'reference':_lift_reference,
    'semaphore':_lift_semaphore,
    'binary_semaphore':_lift_binary_semaphore,
    'setting':_lift_setting,
    'signed_char':_lift_signed_char,
    'signed_int':_lift_signed_int,
    'struct_type':_lift_struct_type,
    'struct_defn':_lift_struct_defn,
    'struct_decl':_lift_struct_decl,
    'struct_ref':_lift_struct_ref,
    'to':_lift_to,
    'type':_lift_type,
    'unary_minus':_lift_unary_minus,
    'unsigned_char':_lift_unsigned_char,
    'unsigned_int':_lift_unsigned_int,
    'uses':_lift_uses,
}

# Sanity checks.
assert all(map(re.compile(r'\w+$').match, LIFT)), 'illegal character in ' \
    'LIFT key; all keys should correspond to grammar rule names'

assert len(list(DONT_LIFT) + list(LIFT)) == len(set(list(DONT_LIFT) +
    list(LIFT))), 'conflicting items present in LIFT and DONT_LIFT'
