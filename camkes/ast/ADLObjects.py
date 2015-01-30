#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''ADL-relevant AST objects. See accompanying docs for more information.'''

from GenericObjects import ASTObject, Reference
import IDLObjects as IDL

class ADLObject(ASTObject):
    pass

class Assembly(ADLObject):
    def __init__(self, name=None, composition=None, configuration=None, filename=None, lineno=-1):
        assert composition is None or isinstance(composition, Composition) \
            or isinstance(composition, Reference)
        assert configuration is None or isinstance(configuration, Configuration) \
            or isinstance(configuration, Reference)
        assert name is None or isinstance(name, str)
        super(Assembly, self).__init__(filename=filename, lineno=lineno)
        self.name = name
        self.composition = composition
        self.configuration = configuration

    def children(self):
        return [self.composition] + ([self.configuration] if self.configuration else [])

    def collapse_references(self):
        self.try_collapse('composition')
        if self.configuration is not None:
            self.try_collapse('configuration')

    def __repr__(self):
        return 'assembly %(name)s { %(composition)s %(configuration)s }' % {
            'name':self.name or '',
            'composition':self.composition,
            'configuration':self.configuration or '',
        }

class Composition(ADLObject):
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

class Configuration(ADLObject):
    def __init__(self, name=None, settings=None, filename=None, lineno=-1):
        assert settings is None or isinstance(settings, list)
        assert name is None or isinstance(name, str)
        super(Configuration, self).__init__(filename=filename, lineno=lineno)
        self.name = name
        self.settings = settings or []

    def children(self):
        return self.settings

    def collapse_references(self):
        self.try_collapse_list('settings')

    def __repr__(self):
        return 'configuration %(name)s { %(settings)s }' % {
            'name':self.name or '',
            'settings':' '.join(map(str, self.settings)),
        }

class Instance(ADLObject):
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

class Connection(ADLObject):
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

class Setting(ADLObject):
    def __init__(self, instance, attribute, value, filename=None, lineno=-1):
        assert isinstance(instance, str)
        assert isinstance(attribute, str)
        super(Setting, self).__init__(filename=filename, lineno=lineno)
        self.instance = instance
        self.attribute = attribute
        self.value = value

    def __repr__(self):
        return '%(instance)s.%(attribute)s = %(value)s;' % self.__dict__

class Component(ADLObject):
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
        self.provides = provides
        self.uses = uses
        self.emits = emits
        self.consumes = consumes
        self.dataports = dataports
        self.attributes = attributes
        self.mutexes = mutexes or []
        self.semaphores = semaphores or []
        self.composition = composition
        self.configuration = configuration

    def children(self):
        ret = self.includes + self.provides + self.uses + self.emits + \
            self.consumes + self.dataports + self.mutexes + self.semaphores
        if self.composition is not None:
            ret.append(self.composition)
        if self.configuration is not None:
            ret.append(self.configuration)
        return ret

    def collapse_references(self):
        for i in ['includes', 'provides', 'uses', 'emits', 'consumes', 'dataports']:
            self.try_collapse_list(i)

        if self.composition is not None:
            self.try_collapse('composition')
        if self.configuration is not None:
            self.try_collapse('configuration')


    def __repr__(self):
        s = '{ %(control)s %(hardware)s %(provides)s %(uses)s %(emits)s %(consumes)s %(dataports)s %(mutexes)s %(semaphores)s %(includes)s }' % {
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
        }
        if self.name:
            s = 'component %(name)s %(defn)s' % {
                'name' : self.name,
                'defn' : s,
            }
        return s

class Interface(ADLObject):
    def __init__(self, filename=None, lineno=-1):
        super(Interface, self).__init__(filename=filename, lineno=lineno)
        self.type = None

    def children(self):
        return [self.type]

    def collapse_references(self):
        self.try_collapse('type')

class Provides(Interface):
    def __init__(self, type, name, filename=None, lineno=-1):
        assert isinstance(type, IDL.Procedure) or isinstance(type, Reference)
        assert isinstance(name, str)
        super(Provides, self).__init__(filename=filename, lineno=lineno)
        self.type = type
        self.name = name

    def __repr__(self):
        return 'provides %(type)s %(name)s;' % self.__dict__

class Uses(Interface):
    def __init__(self, type, name, optional=False, filename=None, lineno=-1):
        assert isinstance(type, IDL.Procedure) or isinstance(type, Reference)
        assert isinstance(name, str)
        super(Uses, self).__init__(filename=filename, lineno=lineno)
        self.type = type
        self.name = name
        self.optional = optional

    def __repr__(self):
        return 'uses %(type)s %(name)s;' % self.__dict__

class Emits(Interface):
    def __init__(self, type, name, filename=None, lineno=-1):
        assert isinstance(type, IDL.Event) or isinstance(type, Reference)
        assert isinstance(name, str)
        super(Emits, self).__init__(filename=filename, lineno=lineno)
        self.type = type
        self.name = name

    def __repr__(self):
        return 'emits %(type)s %(name)s;' % self.__dict__

class Consumes(Interface):
    def __init__(self, type, name, optional=False, filename=None, lineno=-1):
        assert isinstance(type, IDL.Event) or isinstance(type, Reference)
        assert isinstance(name, str)
        super(Consumes, self).__init__(filename=filename, lineno=lineno)
        self.type = type
        self.name = name
        self.optional = optional

    def __repr__(self):
        return 'consumes %(type)s %(name)s;' % self.__dict__

class Dataport(Interface):
    def __init__(self, type, name, optional=False, filename=None, lineno=-1):
        assert isinstance(type, IDL.Port) or isinstance(type, Reference)
        assert isinstance(name, str)
        super(Dataport, self).__init__(filename=filename, lineno=lineno)
        self.type = type
        self.name = name
        self.optional = optional

    def __repr__(self):
        return 'dataport %(type)s %(name)s;' % self.__dict__

class Mutex(ADLObject):
    def __init__(self, name, filename=None, lineno=-1):
        super(Mutex, self).__init__(filename=filename, lineno=lineno)
        self.name = name

    def __repr__(self):
        return 'has mutex %s;' % self.name

class Semaphore(ADLObject):
    def __init__(self, name, filename=None, lineno=-1):
        super(Semaphore, self).__init__(filename=filename, lineno=lineno)
        self.name = name

    def __repr__(self):
        return 'has semaphore %s;' % self.name

class Connector(ADLObject):
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

class Group(ADLObject):
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
