#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''
Objects that can appear in the derived AST. See accompanying docs for more
information.
'''

import collections

class ASTObject(object):
    def __init__(self, filename=None, lineno=-1):
        self.filename = filename
        self.lineno = lineno

    def unresolved(self):
        '''Unresolved references rooted at this element.'''
        return reduce(lambda a, x: a.union(x.unresolved()), self.children(), set())

    @staticmethod
    def externally_resolved():
        '''Whether references to this type should be considered resolved even
        when they are not. Although this sounds like it makes no sense, this is
        actually the behaviour we want for types that are resolved to entities
        outside CAmkES. E.g. port types that typically reference C struct
        types.'''
        return False

    def children(self):
        '''Returns the contained descendents of this object. Override this
        function in types that have children.'''
        return []

    def collapse_references(self):
        pass

    def __eq__(self, other):
        '''Determine if two AST objects are identical. Used for deduping AST
        entries after parsing.'''
        # AST objects must at least have the same type.
        if type(self) != type(other):
            return False

        # Attributes to ignore in comparison.
        ignore = set(['filename', 'lineno'])

        attrs = set(self.__dict__.keys()).difference(ignore)
        other_attrs = set(other.__dict__.keys()).difference(ignore)
        if attrs != other_attrs:
            # The two objects have different attribute NAMES.
            return False
        for i in attrs:
            if getattr(self, i) != getattr(other, i):
                # The two objects have different attribute VALUES.
                return False

        return True

    def __ne__(self, other):
        '''I hate you, Python'''
        return not self == other

    def try_collapse(self, member):
        r = getattr(self, member)
        if isinstance(r, Reference) and r._referent is not None:
            setattr(self, member, r._referent)
        r = getattr(self, member)
        if not isinstance(r, Reference):
            r.collapse_references()

    def try_collapse_list(self, member):
        r = getattr(self, member)
        for i, j in enumerate(r):
            if isinstance(j, Reference) and j._referent is not None:
                r[i] = j._referent
            if not isinstance(r[i], Reference):
                r[i].collapse_references()

class Import(ASTObject):
    def __init__(self, source, relative=True, filename=None, lineno=-1):
        assert isinstance(source, str)
        super(Import, self).__init__(filename=filename, lineno=lineno)
        self.source = source
        self.relative = relative

    def __repr__(self):
        return 'import %(open)s%(source)s%(close)s;' % {
            'open':'"' if self.relative else '<',
            'source':self.source,
            'close':'"' if self.relative else '>',
        }

class Include(ASTObject):
    def __init__(self, source, relative=True, filename=None, lineno=-1):
        assert isinstance(source, str)
        super(Include, self).__init__(filename=filename, lineno=lineno)
        self.source = source
        self.relative = relative

    def __repr__(self):
        return 'include %(open)s%(source)s%(close)s;' % {
            'open':'"' if self.relative else '<',
            'source':self.source,
            'close':'"' if self.relative else '>',
        }

class Reference(ASTObject):
    '''This class encapsulates references to other entities that have been
    parsed.
    '''
    def __init__(self, symbol, symbol_type, filename=None, lineno=-1):
        super(Reference, self).__init__(filename=filename, lineno=lineno)
        assert isinstance(symbol, str)
        self._symbol = symbol
        assert isinstance(symbol_type, type)
        self._type = symbol_type
        self._referent = None

    def unresolved(self):
        if not self._type.externally_resolved() and self._referent is None:
            return set([self])
        else:
            return super(Reference, self).unresolved()

    def children(self):
        # The referent's children if this reference is resolved.
        if self._referent:
            return self._referent.children()
        return []

    def collapse_references(self):
        raise Exception('Collapse references called on a reference itself')

    def resolve_to(self, obj):
        assert isinstance(obj, self._type)
        self._referent = obj

    def __repr__(self):
        # TODO: Can't do this branching until all objects are in one file.
        #if isinstance(self.symbol_type, Composition):
        #    return 'composition %(_symbol)s;' % self.__dict__
        #elif isinstance(self._symbol_type, Configuration):
        #    return 'configuration %(_symbol)s;' % self.__dict__
        #else:
        #    return self._symbol
        return self._symbol

class Assembly(ASTObject):
    def __init__(self, name=None, composition=None, configuration=None, filename=None, lineno=-1):
        assert composition is None or isinstance(composition, Composition) \
            or isinstance(composition, Reference)
        assert configuration is None or isinstance(configuration, Configuration) \
            or isinstance(configuration, Reference)
        assert name is None or isinstance(name, str)
        super(Assembly, self).__init__(filename=filename, lineno=lineno)
        self.name = name
        self.composition = composition
        self.configuration = configuration or Configuration()

    def children(self):
        return [self.composition] + ([self.configuration] if self.configuration else [])

    def collapse_references(self):
        self.try_collapse('composition')
        self.try_collapse('configuration')

    def __repr__(self):
        return 'assembly %(name)s { %(composition)s %(configuration)s }' % {
            'name':self.name or '',
            'composition':self.composition,
            'configuration':self.configuration or '',
        }

class Composition(ASTObject):
    def __init__(self, name=None, instances=None, connections=None, groups=None, filename=None, lineno=-1):
        assert instances is None or isinstance(instances, list)
        assert connections is None or isinstance(connections, list)
        assert name is None or isinstance(name, str)
        super(Composition, self).__init__(filename=filename, lineno=lineno)
        self.name = name
        self.instances = instances or []
        self.connections = connections or []
        self.groups = groups or []
        # All instance and connection names must be unique within a
        # composition. We explicitly check for this here because it is a common
        # user typo.
        uniq = set()
        for x in self.instances + self.connections:
            if x.name in uniq:
                raise Exception('%(filename)s:%(lineno)d: duplicate identifier ' \
                    '\'%(identifier)s\' used in composition \'%(composition)s\'' % {
                        'filename':filename or '<unnamed>',
                        'lineno':lineno,
                        'identifier':x.name,
                        'composition':self.name or '<unnamed>',
                    })
            uniq.add(x.name)

    def children(self):
        return self.instances + self.connections + self.groups

    def collapse_references(self):
        self.try_collapse_list('instances')
        self.try_collapse_list('connections')

    def __repr__(self):
        # Here we need to reconstruct the original groups (and their syntax)
        # because they may have been translated out.
        if len(self.groups) > 0:
            groups = self.groups
        else:
            group_names = [x.address_space for x in self.instances if x]
            groups = []
            for g in group_names:
                groups.append(Group(g, [x for x in self.instances if x.address_space == g]))
        grouped = sum(map(lambda x: x.children(), groups), [])
        return 'composition %(name)s { %(groups)s %(instances)s %(connections)s }' % {
            'name':self.name or '',
            'groups':' '.join(map(str, groups)),
            'instances':' '.join([str(x) for x in self.instances if x not in grouped]),
            'connections':' '.join(map(str, self.connections)),
        }

class Configuration(ASTObject, collections.Mapping):
    def __init__(self, name=None, settings=None, filename=None, lineno=-1):
        assert settings is None or isinstance(settings, list)
        assert name is None or isinstance(name, str)
        super(Configuration, self).__init__(filename=filename, lineno=lineno)
        self.name = name
        self.settings = settings or []
        self.update_mapping()

    def update_mapping(self):
        # Build a two-level dictionary of the attributes, the first level keyed
        # on instance name and the second level keyed on attribute name. This
        # allows more optimised lookups of attributes from templates.
        self.mapping = collections.defaultdict(dict, **{
            instance: {
                s.attribute: s.value for
                    s in filter(lambda x: x.instance == instance, self.settings)
            } for
                instance in set(map(lambda x: x.instance, self.settings))
        })

    def children(self):
        return self.settings

    def collapse_references(self):
        self.try_collapse_list('settings')

    def __repr__(self):
        return 'configuration %(name)s { %(settings)s }' % {
            'name':self.name or '',
            'settings':' '.join(map(str, self.settings)),
        }

    # Implement functions required by collections.Mapping.
    def __getitem__(self, key):
        return self.mapping.__getitem__(key)
    def __iter__(self):
        return self.mapping.__iter__()
    def __len__(self):
        return self.mapping.__len__()

class Instance(ASTObject):
    def __init__(self, type, name, filename=None, lineno=-1):
        assert isinstance(type, Component) or isinstance(type, Reference)
        assert isinstance(name, str)
        super(Instance, self).__init__(filename=filename, lineno=lineno)
        self.type = type
        self.name = name
        self.address_space = None

    def children(self):
        return [self.type]

    def collapse_references(self):
        self.try_collapse('type')

    def __repr__(self):
        return 'component %(type)s %(name)s;' % self.__dict__

class Connection(ASTObject):
    def __init__(self, type, name, from_instance, from_interface, to_instance, to_interface, filename=None, lineno=-1):
        assert isinstance(type, Connector) or isinstance(type, Reference)
        assert isinstance(name, str)
        assert isinstance(from_instance, Instance) or \
            isinstance(from_instance, Reference)
        assert isinstance(from_interface, Interface) or \
            isinstance(from_interface, Reference)
        assert isinstance(to_instance, Instance) or \
            isinstance(to_instance, Reference)
        assert isinstance(to_interface, Interface) or \
            isinstance(to_interface, Reference)
        super(Connection, self).__init__(filename=filename, lineno=lineno)
        self.type = type
        self.name = name
        self.from_instance = from_instance
        self.from_interface = from_interface
        self.to_instance = to_instance
        self.to_interface = to_interface

    def children(self):
        return [self.type, self.from_instance, self.from_interface, self.to_instance, self.to_interface]

    def collapse_references(self):
        for i in ['type', 'from_instance', 'from_interface', 'to_instance', 'to_interface']:
            self.try_collapse(i)

    def __repr__(self):
        return 'connection %(type)s %(name)s(from ' \
            '%(from_instance)s.%(from_interface)s, to ' \
            '%(to_instance)s.%(to_interface)s);' % self.__dict__

class Setting(ASTObject):
    def __init__(self, instance, attribute, value, filename=None, lineno=-1):
        assert isinstance(instance, str)
        assert isinstance(attribute, str)
        super(Setting, self).__init__(filename=filename, lineno=lineno)
        self.instance = instance
        self.attribute = attribute
        self.value = value

    def __repr__(self):
        return '%(instance)s.%(attribute)s = %(value)s;' % self.__dict__

class Component(ASTObject):
    def __init__(self, name=None, includes=None, control=False, hardware=False, \
            provides=None, uses=None, emits=None, consumes=None, dataports=None, \
            attributes=[], mutexes=None, semaphores=None, composition=None, \
            configuration=None, filename=None, lineno=-1):
        assert name is None or isinstance(name, str)
        assert isinstance(control, bool)
        assert isinstance(hardware, bool)
        assert provides is None or isinstance(provides, list)
        assert uses is None or isinstance(uses, list)
        assert emits is None or isinstance(emits, list)
        assert consumes is None or isinstance(consumes, list)
        assert dataports is None or isinstance(dataports, list)
        super(Component, self).__init__(filename=filename, lineno=lineno)
        self.name = name
        self.includes = includes or []
        self.control = control
        self.hardware = hardware
        self.provides = provides or []
        self.uses = uses or []
        self.emits = emits or []
        self.consumes = consumes or []
        self.dataports = dataports or []
        self.attributes = attributes or []
        self.mutexes = mutexes or []
        self.semaphores = semaphores or []
        self.composition = composition
        self.configuration = configuration or Configuration()

    def children(self):
        ret = self.includes + self.provides + self.uses + self.emits + \
            self.consumes + self.dataports + self.mutexes + self.semaphores
        if self.composition is not None:
            ret.append(self.composition)
        ret.append(self.configuration)
        return ret

    def collapse_references(self):
        for i in ['includes', 'provides', 'uses', 'emits', 'consumes', 'dataports']:
            self.try_collapse_list(i)

        if self.composition is not None:
            self.try_collapse('composition')
        self.try_collapse('configuration')


    def __repr__(self):
        s = '{ %(control)s %(hardware)s %(provides)s %(uses)s %(emits)s %(consumes)s %(dataports)s %(mutexes)s %(semaphores)s %(includes)s %(composition)s %(configuration)s}' % {
            'control':'control;' if self.control else '',
            'hardware':'hardware;' if self.hardware else '',
            'provides':' '.join(map(str, self.provides)),
            'uses':' '.join(map(str, self.uses)),
            'emits':' '.join(map(str, self.emits)),
            'consumes':' '.join(map(str, self.consumes)),
            'dataports':' '.join(map(str, self.dataports)),
            'mutexes':' '.join(map(str, self.mutexes)),
            'semaphores':' '.join(map(str, self.semaphores)),
            'includes':' '.join(map(str, self.includes)),
            'attributes':' '.join(map(str, self.attributes)),
            'composition':self.composition or '',
            'configuration':self.configuration or ''
        }
        if self.name:
            s = 'component %(name)s %(defn)s' % {
                'name' : self.name,
                'defn' : s,
            }
        return s

class Interface(ASTObject):
    def __init__(self, filename=None, lineno=-1):
        super(Interface, self).__init__(filename=filename, lineno=lineno)
        self.type = None

    def children(self):
        return [self.type]

    def collapse_references(self):
        self.try_collapse('type')

class Provides(Interface):
    def __init__(self, type, name, filename=None, lineno=-1):
        assert isinstance(type, Procedure) or isinstance(type, Reference)
        assert isinstance(name, str)
        super(Provides, self).__init__(filename=filename, lineno=lineno)
        self.type = type
        self.name = name

    def __repr__(self):
        return 'provides %(type)s %(name)s;' % self.__dict__

class Uses(Interface):
    def __init__(self, type, name, optional=False, filename=None, lineno=-1):
        assert isinstance(type, Procedure) or isinstance(type, Reference)
        assert isinstance(name, str)
        super(Uses, self).__init__(filename=filename, lineno=lineno)
        self.type = type
        self.name = name
        self.optional = optional

    def __repr__(self):
        return 'uses %(type)s %(name)s;' % self.__dict__

class Emits(Interface):
    def __init__(self, type, name, filename=None, lineno=-1):
        assert isinstance(type, Event) or isinstance(type, Reference)
        assert isinstance(name, str)
        super(Emits, self).__init__(filename=filename, lineno=lineno)
        self.type = type
        self.name = name

    def __repr__(self):
        return 'emits %(type)s %(name)s;' % self.__dict__

class Consumes(Interface):
    def __init__(self, type, name, optional=False, filename=None, lineno=-1):
        assert isinstance(type, Event) or isinstance(type, Reference)
        assert isinstance(name, str)
        super(Consumes, self).__init__(filename=filename, lineno=lineno)
        self.type = type
        self.name = name
        self.optional = optional

    def __repr__(self):
        return 'consumes %(type)s %(name)s;' % self.__dict__

class Dataport(Interface):
    def __init__(self, type, name, optional=False, filename=None, lineno=-1):
        assert isinstance(type, Port) or isinstance(type, Reference)
        assert isinstance(name, str)
        super(Dataport, self).__init__(filename=filename, lineno=lineno)
        self.type = type
        self.name = name
        self.optional = optional

    def __repr__(self):
        return 'dataport %(type)s %(name)s;' % self.__dict__

class Mutex(ASTObject):
    def __init__(self, name, filename=None, lineno=-1):
        super(Mutex, self).__init__(filename=filename, lineno=lineno)
        self.name = name

    def __repr__(self):
        return 'has mutex %s;' % self.name

class Semaphore(ASTObject):
    def __init__(self, name, filename=None, lineno=-1):
        super(Semaphore, self).__init__(filename=filename, lineno=lineno)
        self.name = name

    def __repr__(self):
        return 'has semaphore %s;' % self.name

class Connector(ASTObject):
    def __init__(self, name=None, from_type='Interface', to_type='Interface', from_template=None, to_template=None, filename=None, lineno=-1):
        assert isinstance(from_type, str) and \
            from_type in ['Event', 'Interface', 'Procedure', 'Dataport']
        assert isinstance(to_type, str) and \
            to_type in ['Event', 'Interface', 'Procedure', 'Dataport']
        assert name is None or isinstance(name, str)
        super(Connector, self).__init__(filename=filename, lineno=lineno)
        self.name = name
        self.from_type = from_type
        self.to_type = to_type
        self.from_template = from_template
        self.to_template = to_template
        # TODO: Symbol name for from and to is not currently represented.
        # Is this necessary?

    def __repr__(self):
        s = '{ from %(from_type)s i_from; to %(to_type)s i_to; }' % self.__dict__
        if self.name:
            s = 'connector %(name)s %(defn)s' % {
                'name':self.name,
                'defn':s,
            }
        return s

class Group(ASTObject):
    def __init__(self, name=None, instances=None, filename=None, lineno=-1):
        super(Group, self).__init__(filename=filename, lineno=lineno)
        self.name = name
        self.instances = instances or []

    def children(self):
        return self.instances

    def __repr__(self):
        s = 'group '
        if self.name is not None:
            s += '%s ' % self.name
        s += '{ %s }' % ''.join(map(str, self.instances))
        return s

class Procedure(ASTObject):
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
        s = '{ %(includes)s %(methods)s }' % {
            'includes':' '.join(map(str, self.includes)),
            'methods':' '.join(map(str, self.methods)),
        }
        if self.name:
            s = 'procedure %(name)s %(defn)s' % {
                'name':self.name,
                'defn':s,
            }
        return s

class Method(ASTObject):
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

class Attribute(ASTObject):
    def __init__(self, type, name, filename=None, lineno=-1):
        assert isinstance(name, str)
        super(Attribute, self).__init__(filename=filename, lineno=lineno)
        self.name = name
        self.type = type

    def __repr__(self):
        return 'attribute %(type)s %(name)s;' % self.__dict__

class Parameter(ASTObject):
    def __init__(self, name, direction, type, array=False, filename=None, lineno=-1):
        assert isinstance(name, str)
        super(Parameter, self).__init__(filename=filename, lineno=lineno)
        self.name = name
        self.direction = direction
        self.type = type
        self.array = array

    def __repr__(self):
        return '%(direction)s %(type)s %(name)s' % self.__dict__

class Type(ASTObject):
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

class Event(ASTObject):
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

class Port(ASTObject):
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
