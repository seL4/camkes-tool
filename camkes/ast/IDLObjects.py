#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''IDL-relevant AST objects. See accompanying docs for more information.'''

import GenericObjects

class IDLObject(GenericObjects.ASTObject):
    pass

class Procedure(IDLObject):
    def __init__(self, name=None, includes=None, methods=None, attributes=None, filename=None, lineno=-1):
        assert name is None or isinstance(name, str)
        assert methods is None or isinstance(methods, list)
        assert attributes is None or isinstance(attributes, list)
        super(Procedure, self).__init__(filename=filename, lineno=lineno)
        self.name = name
        self.includes = includes or []
        self.methods = methods or []
        self.attributes = attributes or []

    def children(self):
        return self.includes + self.methods + self.attributes

    def collapse_references(self):
        for i in ['includes', 'methods', 'attributes']:
            self.try_collapse_list(i)

    def __repr__(self):
        s = '{ %s }' % ' '.join(map(str, self.methods))
        if self.name:
            s = 'procedure %(name)s %(defn)s' % {
                'name':self.name,
                'defn':s,
            }
        return s

class Method(IDLObject):
    def __init__(self, name, return_type, parameters, filename=None, lineno=-1):
        assert isinstance(name, str)
        assert isinstance(parameters, list)
        for i in parameters: assert isinstance(i, Parameter)
        super(Method, self).__init__(filename=filename, lineno=lineno)
        self.name = name
        self.return_type = return_type
        self.parameters = parameters

    def children(self):
        return ([self.return_type] if self.return_type else []) + self.parameters

    def collapse_references(self):
        if self.return_type is not None:
            self.try_collapse('return_type')
        self.try_collapse_list('parameters')

    def __repr__(self):
        return '%(return_type)s %(name)s(%(parameters)s);' % {
            'return_type':self.return_type or 'void',
            'name':self.name,
            'parameters':' '.join(map(str, self.parameters)),
        }

class Attribute(IDLObject):
    def __init__(self, type, name, filename=None, lineno=-1):
        assert isinstance(name, str)
        super(Attribute, self).__init__(filename=filename, lineno=lineno)
        self.name = name
        self.type = type

    def __repr__(self):
        return 'attribute %(type)s %(name)s;' % self.__dict__

class Parameter(IDLObject):
    def __init__(self, name, direction, type, array=False, filename=None, lineno=-1):
        assert isinstance(name, str)
        super(Parameter, self).__init__(filename=filename, lineno=lineno)
        self.name = name
        self.direction = direction
        self.type = type
        self.array = array

    def __repr__(self):
        return '%(direction)s %(type)s %(name)s' % self.__dict__

class Type(IDLObject):
    def __init__(self, type, filename=None, lineno=-1):
        # Map of all the possible parsed input types to their canonical form
        normalisation = {
            'int'              : 'int',
            'integer'          : 'int',
            'signed int'       : 'int',
            'unsigned int'     : 'unsigned int',
            'unsigned integer' : 'unsigned int',
            'int8_t'           : 'int8_t',
            'int16_t'          : 'int16_t',
            'int32_t'          : 'int32_t',
            'int64_t'          : 'int64_t',
            'uint8_t'          : 'uint8_t',
            'uint16_t'         : 'uint16_t',
            'uint32_t'         : 'uint32_t',
            'uint64_t'         : 'uint64_t',
            'real'             : 'real',
            'double'           : 'double',
            'float'            : 'float',
            'uintptr_t'        : 'uintptr_t',
            'char'             : 'char',
            'character'        : 'character',
            'boolean'          : 'boolean',
            'bool'             : 'boolean',
            'string'           : 'string',
        }
        assert isinstance(type, str)
        assert type in normalisation
        super(Type, self).__init__(filename=filename, lineno=lineno)
        self.type = normalisation[type]

    @staticmethod
    def externally_resolved():
        return True

    def __repr__(self):
        return self.type

class Direction(IDLObject):
    def __init__(self, direction, filename=None, lineno=-1):
        assert isinstance(direction, str)
        assert direction in ['refin', 'in', 'inout', 'out']
        super(Direction, self).__init__(filename=filename, lineno=lineno)
        self.direction = direction

    def __repr__(self):
        return self.direction

class Event(IDLObject):
    def __init__(self, name=None, id=0, filename=None, lineno=-1):
        assert name is None or isinstance(name, str)
        assert isinstance(id, int)
        super(Event, self).__init__(filename=filename, lineno=lineno)
        self.name = name
        self.id = id

    @staticmethod
    def externally_resolved():
        return True

    def __repr__(self):
        # TODO: Standardise this as CAmkES currently has no syntax for defining
        # events.
        return 'event %(name)s = %(id)s;' % self.__dict__

class Port(IDLObject):
    def __init__(self, name=None, type=None, filename=None, lineno=-1):
        assert name is None or isinstance(name, str)
        assert type is None or isinstance(type, str)
        super(Port, self).__init__(filename=filename, lineno=lineno)
        self.name = name
        self.type = None if type in ['None', 'Buf'] else type

    @staticmethod
    def externally_resolved():
        return True

    def __repr__(self):
        return 'dataport %(type)s %(name)s;' % {
            'type':self.type or 'Buf',
            'name':self.name,
        }
