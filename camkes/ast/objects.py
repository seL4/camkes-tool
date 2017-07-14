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
Objects that can appear in the derived AST. See accompanying docs for more
information.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

from .base import ASTObject, MapLike
from .ckeywords import C_KEYWORDS
from .exception import ASTError
from .location import SourceLocation
from camkes.internal.frozendict import frozendict
import abc, collections, itertools, numbers, six

def types_compatible(value, attribute):
    type = attribute.type;
    assert isinstance(type, (six.string_types, Struct))
    if attribute.array is True:
        assert isinstance(value, (tuple, list))
        values = value
    else:
        values = (value,)
    for value in values:
        if isinstance(type, six.string_types):
            if (isinstance(value, six.integer_types) and type != 'int'):
                return (False, "For \"%s\": required type is \"%s\", value is \"int\"" % (str(value), type))
            if (isinstance(value, float) and type not in ('double', 'float')):
                return (False, "For \"%s\": required type is \"%s\", value is \"float\"" % (str(value), type))
            if (isinstance(value, six.string_types) and type != 'string'):
                return (False, "For \"%s\": required type is \"%s\", value is \"string\"" % (str(value), type))
            if (isinstance(value, list) and type != 'list'):
                return (False, "For \"%s\": required type is \"%s\", value is \"list\"" % (str(value), type))
            if ((isinstance(value, dict) and type != 'dict')):
                return (False, "For \"%s\": required type is \"%s\", value is \"dict\"" % (str(value), type))

        elif isinstance(type, Struct):
            attr_names = {x.name for x in type.attributes}
            missing_attrs = list(attr_names - set(value.keys()))
            if len(missing_attrs) != 0:
                new_missing = []
                for attr in missing_attrs:
                    # Use default attribute if value not present in setting array
                    attribute = next(a for a in type.attributes if a.name == attr)
                    if attribute.default is not None:
                        value[attr] = attribute.default
                    else:
                        new_missing.append(attr)
                if len(new_missing) != 0:
                    return (False, "Attributes: \"%s\" are missing from assignment." % new_missing)

            extra_attrs = list(set(value.keys())- attr_names)
            if len(extra_attrs) != 0:
                return (False, "Attributes: \"%s\" do not exist in \"%s\" definition." %(extra_attrs, type.name))

            for x in type.attributes:
                (compat, error_str) = types_compatible(value[x.name], x)
                if not compat:
                    return (False, error_str)
    return (True, "")

class Include(ASTObject):
    def __init__(self, source, relative=True, location=None):
        assert isinstance(source, six.string_types)
        assert isinstance(relative, bool)
        super(Include, self).__init__(location)
        self._source = source
        self._relative = relative

    @property
    def source(self):
        return self._source
    @source.setter
    def source(self, value):
        assert isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot change the source of a frozen include')
        self._source = value

    @property
    def relative(self):
        return self._relative
    @relative.setter
    def relative(self, value):
        assert isinstance(value, bool)
        if self.frozen:
            raise TypeError('you cannot change the relative value of a frozen '
                'include')
        self._relative = value

class Reference(ASTObject):
    '''This class encapsulates references to other entities that have been
    parsed.
    '''
    def __init__(self, symbol, symbol_type, location=None):
        assert isinstance(symbol, list) and len(symbol) > 0 and \
            all([isinstance(x, six.string_types) for x in symbol])
        assert symbol_type is None or isinstance(symbol_type, type)
        super(Reference, self).__init__(location)
        self.name = symbol
        self.type = symbol_type

    def freeze(self):
        raise ASTError('reference remaining in frozen AST tree', self)

class Assembly(ASTObject):
    child_fields = ('composition', 'configuration')

    def __init__(self, name=None, composition=None, configuration=None, location=None):
        assert name is None or isinstance(name, six.string_types)
        assert composition is None or isinstance(composition, (Composition,
            Reference))
        assert configuration is None or isinstance(configuration,
            (Configuration, Reference))
        super(Assembly, self).__init__(location)
        self._name = name
        self._composition = composition
        if configuration is None:
            configuration = Configuration()
        self._configuration = configuration
        self.claim_children()

    @property
    def name(self):
        return self._name
    @name.setter
    def name(self, value):
        assert value is None or isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot change the name of a frozen assembly')
        self._name = value

    @property
    def composition(self):
        return self._composition
    @composition.setter
    def composition(self, value):
        assert isinstance(value, (Composition, Reference))
        if self.frozen:
            raise TypeError('you cannot change the composition of a frozen '
                'assembly')
        self._composition = value

    @property
    def configuration(self):
        return self._configuration
    @configuration.setter
    def configuration(self, value):
        assert isinstance(value, (Configuration, Reference))
        if self.frozen:
            raise TypeError('you cannot change the configuration of a frozen '
                'assembly')
        self._configuration = value

    def claim_children(self):
        self.adopt(self.composition)
        self.adopt(self.configuration)

    def freeze(self):
        if self.frozen:
            return
        for s in self.configuration.settings:
            for i in self.composition.instances:
                if i.name == s.instance:
                    break
            else:
                continue
            for a in i.type.attributes:
                if a.name == s.attribute:
                    break
            else:
                continue
            (result, error_str) = types_compatible(s.value, a)
            if not result:
                raise ASTError('mistyped assignment of attribute of type %s: %s' %
                    (str(a.type), error_str), s)
        super(Assembly, self).freeze()

    def get_attribute(self, instance_name, attribute_name):
        '''
        Get an attribute from an instance from an assembly
        '''
        instance_gen = (x for x in self.instances if x.name == instance_name)
        try:
            instance = next(instance_gen)
            attribute_gen = (x for x in instance.type.attributes
                            if x.name == attribute_name)
            return next(attribute_gen)
        except StopIteration:
            # couldn't find attribute
            return None

    # Shortcuts for accessing grandchildren.
    @property
    def instances(self):
        return self.composition.instances
    @property
    def connections(self):
        return self.composition.connections
    @property
    def settings(self):
        return self.configuration.settings

class Composition(MapLike):
    # Note that the ordering of these child fields is important as members of
    # `connections` and `exports` may reference members of `instances` and/or
    # `groups`, so both of the latter need to be seen by scoping resolution
    # before the former.
    child_fields = ('instances', 'groups', 'connections', 'exports')

    def __init__(self, name=None, instances=None, connections=None,
            groups=None, exports=None, location=None):
        assert name is None or isinstance(name, six.string_types)
        assert instances is None or (isinstance(instances, (list, tuple)) and
            all(isinstance(x, (Instance, Reference)) for x in instances))
        assert connections is None or (isinstance(connections, (list, tuple))
            and all(isinstance(x, (Connection, Reference)) for x in
            connections))
        assert groups is None or (isinstance(groups, (list, tuple)) and
            all(isinstance(x, (Group, Reference)) for x in groups))
        assert exports is None or (isinstance(exports, (list, tuple)) and
            all(isinstance(x, (Export, Reference)) for x in exports))
        super(Composition, self).__init__(location)
        self._name = name
        self._instances = list(instances or [])
        self._connections = list(connections or [])
        self._groups = list(groups or [])
        self._exports = list(exports or [])
        self.claim_children()

    @property
    def name(self):
        return self._name
    @name.setter
    def name(self, value):
        assert value is None or isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot change the name of a frozen '
                'composition')
        self._name = value

    @property
    def instances(self):
        return self._instances
    @instances.setter
    def instances(self, value):
        assert isinstance(value, (list, tuple)) and \
            all(isinstance(x, (Instance, Reference)) for x in value)
        if self.frozen:
            raise TypeError('you cannot change the instances of a frozen '
                'composition')
        self._instances = value

    @property
    def connections(self):
        return self._connections
    @connections.setter
    def connections(self, value):
        assert isinstance(value, (list, tuple)) and \
            all(isinstance(x, (Connection, Reference)) for x in value)
        if self.frozen:
            raise TypeError('you cannot change the connections of a frozen '
                'composition')
        self._connections = value

    @property
    def groups(self):
        return self._groups
    @groups.setter
    def groups(self, value):
        assert isinstance(value, (list, tuple)) and \
            all(isinstance(x, (Group, Reference)) for x in value)
        if self.frozen:
            raise TypeError('you cannot change the groups of a frozen '
                'composition')
        self._groups = value

    @property
    def exports(self):
        return self._exports
    @exports.setter
    def exports(self, value):
        assert isinstance(value, (list, tuple)) and \
            all(isinstance(x, (Export, Reference)) for x in value)
        if self.frozen:
            raise TypeError('you cannot change the exports of a frozen '
                'composition')
        self._exports = value

    def claim_children(self):
        [self.adopt(i) for i in self.instances]
        [self.adopt(c) for c in self.connections]
        [self.adopt(g) for g in self.groups]
        [self.adopt(e) for e in self.exports]

    def freeze(self):
        if isinstance(self.parent, Assembly):
            # Check that the specification doesn't connect the same interface
            # twice and all required interfaces are connected. Note that this
            # only need to be true of the final, top-level composition.
            unconnected = set()
            connected = set()
            for i in self.instances:
                for inf in itertools.chain(i.type.consumes, i.type.dataports,
                        i.type.emits, i.type.provides, i.type.uses):
                    unconnected.add((i, inf))
            for conn in self.connections:
                for end in itertools.chain(conn.from_ends, conn.to_ends):
                    if (end.instance, end.interface) in connected:
                        raise ASTError('duplicate use of interface %s.%s '
                            '(deprecated form of N-way connections?)' %
                            (end.instance.name, end.interface.name), end)
                    assert (end.instance, end.interface) in unconnected, \
                        'connection end %s.%s seems to refer to an interface ' \
                        'that doesn\'t exist (bug in AST freezing?)' % \
                        (end.instance.name, end.interface.name)
                    unconnected.remove((end.instance, end.interface))
                    connected.add((end.instance, end.interface))
            for i, inf in unconnected:
                if (not hasattr(inf, 'optional') or not inf.optional) and not \
                        isinstance(inf, (Emits, Provides)):
                    # For a simple specification, this is immediately an error.
                    # However, in a hierarchical specification, this interface
                    # may actually be a phony "virtual" interface that is
                    # exporting a nested component's interface. Check that it
                    # is not before throwing an error.
                    if i.type.composition is not None and len([x for x in
                            i.type.composition.exports if x.destination ==
                            inf]) > 0:
                        continue
                    raise ASTError('non-optional interface %s.%s is not '
                        'connected' % (i.name, inf.name), i)
        self.instances = tuple(self.instances)
        self.connections = tuple(self.connections)
        self.groups = tuple(self.groups)
        self.exports = tuple(self.exports)
        super(Composition, self).freeze()

class Configuration(MapLike):
    child_fields = ('settings',)

    def __init__(self, name=None, settings=None, location=None):
        assert name is None or isinstance(name, six.string_types)
        assert settings is None or isinstance(settings, (list, tuple))
        super(Configuration, self).__init__(location)
        self._name = name
        self._settings = list(settings or [])
        self.settings_dict = {}
        self.claim_children()

    @property
    def name(self):
        return self._name
    @name.setter
    def name(self, value):
        assert value is None or isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot change the name of a frozen '
                'configuration')
        self._name = value

    @property
    def settings(self):
        return self._settings
    @settings.setter
    def settings(self, value):
        assert isinstance(value, (list, tuple))
        if self.frozen:
            raise TypeError('you cannot change the settings of a frozen '
                'configuration')
        self._settings = value

    def claim_children(self):
        [self.adopt(s) for s in self.settings]

    def freeze(self):
        if self.frozen:
            return
        self.settings = tuple(self.settings)
        # Jump MapLike
        ASTObject.freeze(self)
        self._mapping = collections.defaultdict(dict)
        for s in self.settings:
            if s.attribute in self._mapping[s.instance]:
                raise ASTError('duplicate setting for attribute '
                    '\'%s.%s\'' % (s.instance, s.attribute), s)
            self._mapping[s.instance][s.attribute] = s.value

            if s.instance in self.settings_dict:
                self.settings_dict[s.instance][s.attribute] = s
            else:
                self.settings_dict[s.instance] = {s.attribute: s}

        # Add any default values of attributes that were not set.
        if isinstance(self.parent, Assembly):
            for i in self.parent.composition.instances:
                for a in i.type.attributes:
                    if (i.name not in self._mapping or
                        a.name not in self._mapping[i.name]) and \
                            a.default is not None:
                        self._mapping[i.name][a.name] = a.default

class Instance(ASTObject):
    child_fields = ('type',)

    def __init__(self, type, name, location=None):
        assert isinstance(type, (Component, Reference))
        assert isinstance(name, six.string_types)
        super(Instance, self).__init__(location)
        self._type = type
        self._name = name
        self._address_space = name

    @property
    def type(self):
        return self._type
    @type.setter
    def type(self, value):
        assert isinstance(value, (Component, Reference))
        if self.frozen:
            raise TypeError('you cannot change the type of a frozen instance')
        self._type = value

    @property
    def name(self):
        return self._name
    @name.setter
    def name(self, value):
        assert isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot change the name of a frozen instance')
        self._name = value

    @property
    def address_space(self):
        return self._address_space
    @address_space.setter
    def address_space(self, value):
        assert isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot change the address space of a frozen '
                'instance')
        self._address_space = value

    def label(self):
        return self.name

    @property
    def instance(self):
        return self

    def __str__(self):
        return self.name

class Connection(ASTObject):
    child_fields = ('from_ends', 'to_ends', 'type')

    def __init__(self, connection_type, name, from_ends, to_ends, location=None):
        assert isinstance(connection_type, (Connector, Reference))
        assert isinstance(name, six.string_types)
        assert from_ends is None or isinstance(from_ends, (list, tuple))
        assert to_ends is None or isinstance(to_ends, (list, tuple))
        super(Connection, self).__init__(location)
        self._type = connection_type
        self._name = name
        self._from_ends = from_ends
        self._to_ends = to_ends
        self.claim_children()

    @property
    def type(self):
        return self._type
    @type.setter
    def type(self, value):
        assert isinstance(value, (Connector, Reference))
        if self.frozen:
            raise TypeError('you cannot change the type of a frozen '
                'connection')
        self._type = value

    @property
    def name(self):
        return self._name
    @name.setter
    def name(self, value):
        assert isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot change the name of a frozen '
                'connection')
        self._name = value

    @property
    def from_ends(self):
        return self._from_ends
    @from_ends.setter
    def from_ends(self, value):
        assert isinstance(value, (list, tuple))
        if self.frozen:
            raise TypeError('you cannot change the from ends of a frozen '
                'connection')
        self._from_ends = value

    @property
    def to_ends(self):
        return self._to_ends
    @to_ends.setter
    def to_ends(self, value):
        assert isinstance(value, (list, tuple))
        if self.frozen:
            raise TypeError('you cannot change the to ends of a frozen '
                'connection')
        self._to_ends = value

    def claim_children(self):
        [self.adopt(e) for e in self.from_ends]
        [self.adopt(e) for e in self.to_ends]

    def freeze(self):
        if self.frozen:
            return
        self.from_ends = tuple(self.from_ends)
        self.to_ends = tuple(self.to_ends)
        super(Connection, self).freeze()
        if len(self.from_ends) == 0:
            raise ASTError('connection \'%s\' has no from ends' % self.name,
                self)
        if len(self.to_ends) == 0:
            raise ASTError('connection \'%s\' has no to ends' % self.name,
                self)
        if len(self.from_ends) > 1 and not self.type.from_multiple:
            raise ASTError('connection \'%s\' has multiple from ends '
                'but its connector type (%s) only permits one'
                % (self.name, self.type.name), self)
        if len(self.to_ends) > 1 and not self.type.to_multiple:
            raise ASTError('connection \'%s\' has multiple to ends '
                'but its connector type (%s) only permits one'
                % (self.name, self.type.name), self)
        types = set([e.interface.type for e in self.from_ends] +
            [e.interface.type for e in self.to_ends])
        if len(types) > 1:
            raise ASTError('multiple conflicting types for the '
                'interfaces of connection \'%s\': %s' % (self.name,
                ', '.join(types)), self)
        for f in self.from_ends:
            if not isinstance(f.interface, Emits) and not \
                    isinstance(f.interface, Uses) and not \
                    isinstance(f.interface, Dataport):
                if f.instance is None:
                    name = f.interface.name
                else:
                    name = '%s.%s' % (f.instance.name, f.interface.name)
                raise ASTError('connection \'%s\' has an end %s that cannot be '
                    'used as \'from\'' % (self.name, name), self)
            if self.type.from_hardware and not f.get_end_type().hardware:
                raise ASTError('connection \'%s\' has a type \'%s\' that is '
                    'intended for connecting from hardware devices, but end '
                    '%s.%s refers to a software component' % (self.name,
                    self.type.name, f.instance.name, f.interface.name), f)
            if not self.type.from_hardware and f.get_end_type().hardware:
                raise ASTError('connection \'%s\' has a type \'%s\' that is '
                    'intended for connecting from software components, but '
                    'end %s.%s refers to a hardware device' % (self.name,
                    self.type.name, f.instance.name, f.interface.name), f)
            if self.type.from_type == 'Event' and not \
                    isinstance(f.interface, Emits):
                raise ASTError('connection \'%s\' has a type \'%s\' that is '
                    'intended for connecting from events, but end %s.%s is '
                    'not an emitted event' % (self.name, self.type.name,
                    f.instance.name, f.interface.name), f)
            if self.type.from_type == 'Procedure' and not \
                    isinstance(f.interface, Uses):
                raise ASTError('connection \'%s\' has a type \'%s\' that is '
                    'intended for connecting from procedures, but end %s.%s '
                    'is not a used procedure' % (self.name, self.type.name,
                    f.instance.name, f.interface.name), f)
            if self.type.from_type == 'Dataport' and not \
                    isinstance(f.interface, Dataport):
                raise ASTError('connection \'%s\' has a type \'%s\' that is '
                    'intended for connecting from dataports, but end %s.%s '
                    'is not a dataport' % (self.name, self.type.name,
                    f.instance.name, f.interface.name), f)
        for t in self.to_ends:
            if not isinstance(t.interface, Consumes) and not \
                    isinstance(t.interface, Provides) and not \
                    isinstance(t.interface, Dataport):
                if t.instance is None:
                    name = t.interface.name
                else:
                    name = '%s.%s' % (t.instance.name, t.interface.name)
                raise ASTError('connection \'%s\' has an end %s that cannot be '
                    'used as \'to\'' % (self.name, name), self)
            if self.type.to_hardware and not t.get_end_type().hardware:
                raise ASTError('connection \'%s\' has a type \'%s\' that is '
                    'intended for connecting to hardware devices, but end '
                    '%s.%s refers to a software component' % (self.name,
                    self.type.name, t.instance.name, t.interface.name), t)
            if not self.type.to_hardware and t.get_end_type().hardware:
                raise ASTError('connection \'%s\' has a type \'%s\' that is '
                    'intended for connecting to software components, but end '
                    '%s.%s refers to a hardware device' % (self.name,
                    self.type.name, t.instance.name, t.interface.name), t)
            if self.type.to_type == 'Event' and not \
                    isinstance(t.interface, Consumes):
                raise ASTError('connection \'%s\' has a type \'%s\' that is '
                    'intended for connecting to events, but end %s.%s is '
                    'not a consumed event' % (self.name, self.type.name,
                    t.instance.name, t.interface.name), t)
            if self.type.to_type == 'Procedure' and not \
                    isinstance(t.interface, Provides):
                raise ASTError('connection \'%s\' has a type \'%s\' that is '
                    'intended for connecting to procedures, but end %s.%s '
                    'is not a provided procedure' % (self.name, self.type.name,
                    t.instance.name, t.interface.name), t)
            if self.type.to_type == 'Dataport' and not \
                    isinstance(t.interface, Dataport):
                raise ASTError('connection \'%s\' has a type \'%s\' that is '
                    'intended for connecting to dataports, but end %s.%s '
                    'is not a dataport' % (self.name, self.type.name,
                    t.instance.name, t.interface.name), t)

    # Convenience members for dealing with connections that we know are
    # one-to-one.
    @property
    def from_end(self):
        assert len(self.from_ends) == 1, 'accessing a connection with ' \
            'multiple from ends as if it only has one'
        return self.from_ends[0]
    @property
    def to_end(self):
        assert len(self.to_ends) == 1, 'accessing a connection with ' \
            'multiple to ends as if it only has one'
        return self.to_ends[0]
    @property
    def from_instance(self):
        return self.from_end.instance
    @property
    def from_interface(self):
        return self.from_end.interface
    @property
    def to_instance(self):
        return self.to_end.instance
    @property
    def to_interface(self):
        return self.to_end.interface

    def label(self):
        return self.name

class Setting(ASTObject):
    def __init__(self, instance, attribute, value, location=None):
        assert isinstance(instance, six.string_types)
        assert isinstance(attribute, six.string_types)
        assert isinstance(value, (numbers.Number, list, dict,
            AttributeReference) + six.string_types)
        super(Setting, self).__init__(location)
        self._instance = instance
        self._attribute = attribute
        self._value = value
        if isinstance(value, Reference):
            self.child_fields = ('value',)

    @property
    def instance(self):
        return self._instance
    @instance.setter
    def instance(self, value):
        assert isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot change the instance of a frozen '
                'setting')
        self._instance = value

    @property
    def attribute(self):
        return self._attribute
    @attribute.setter
    def attribute(self, value):
        assert isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot change the attribute name of a frozen '
                'setting')
        self._attribute = value

    @property
    def value(self):
        return self._value
    @value.setter
    def value(self, value):
        assert isinstance(value, (numbers.Number, list, dict,
            AttributeReference, tuple, frozendict) + six.string_types)
        if self.frozen:
            raise TypeError('you cannot change the value of a frozen setting')
        self._value = value
        if isinstance(value, (Attribute, Reference)):
            self.child_fields = ('value',)
        else:
            self.child_fields = ()

    def freeze(self):
        if self.frozen:
            return
        if isinstance(self.value, Reference):
            raise ASTError('setting %s.%s is a reference with no resolved '
                'value' % (self.instance, self.attribute), self)
        if self.attribute in C_KEYWORDS:
            raise ASTError('setting name \'%s\' clashes with a C keyword' %
                self.attribute, self)
        if isinstance(self.value, list):
            self.value = tuple(self.value)
        elif isinstance(self.value, dict):
            self.value = frozendict(self.value)
        super(Setting, self).freeze()

class Struct(ASTObject):
    child_fields = ('attributes',)
    anon_struct_count = 0
    def __init__(self, name=None, attributes=None, location=None):
        assert name is None or isinstance(name, six.string_types)
        assert attributes is None or (isinstance(attributes, (list, tuple)) and
            all(isinstance(x, Attribute) for x in attributes))
        super(Struct, self).__init__(location)

        if name is None:
            # Generate a struct name as none was provided.
            name = "camkes_anon_struct_%d" % Struct.anon_struct_count
            Struct.anon_struct_count = Struct.anon_struct_count + 1
        self._name = name
        self._attributes = list(attributes or [])

    def __str__(self):
        return self.name

    @property
    def name(self):
        return self._name
    @name.setter
    def name(self, value):
        assert value is None or isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot change the name of a frozen struct')
        self._name = value

    @property
    def attributes(self):
        return self._attributes
    @attributes.setter
    def attributes(self, value):
        assert isinstance(value, (list, tuple)) and \
            all(isinstance(x, Attribute) for x in value)
        if self.frozen:
            raise TypeError('you cannot change the attributes of a frozen '
                'struct')
        self._attributes = value

    def freeze(self):
        if self.frozen:
            return
        self.attributes = tuple(self.attributes)
        super(Struct, self).freeze()

class Component(MapLike):
    child_fields = ('attributes', 'includes', 'provides', 'uses', 'emits',
        'consumes', 'dataports', 'mutexes', 'semaphores', 'binary_semaphores', 'composition',
        'configuration')

    def __init__(self, name=None, includes=None, control=False, hardware=False,
            provides=None, uses=None, emits=None, consumes=None, dataports=None,
            attributes=None, mutexes=None, semaphores=None, binary_semaphores=None, composition=None,
            configuration=None, location=None):
        assert name is None or isinstance(name, six.string_types)
        assert includes is None or (isinstance(includes, (list, tuple)) and
            all(isinstance(x, Include) for x in includes))
        assert isinstance(control, bool)
        assert isinstance(hardware, bool)
        assert provides is None or (isinstance(provides, (list, tuple)) and
            all(isinstance(x, Provides) for x in provides))
        assert uses is None or (isinstance(uses, (list, tuple)) and
            all(isinstance(x, Uses) for x in uses))
        assert emits is None or (isinstance(emits, (list, tuple)) and
            all(isinstance(x, Emits) for x in emits))
        assert consumes is None or (isinstance(consumes, (list, tuple)) and
            all(isinstance(x, Consumes) for x in consumes))
        assert dataports is None or (isinstance(dataports, (list, tuple)) and
            all(isinstance(x, Dataport) for x in dataports))
        assert attributes is None or (isinstance(attributes, (list, tuple)) and
            all(isinstance(x, Attribute) for x in attributes))
        assert mutexes is None or (isinstance(mutexes, (list, tuple)) and
            all(isinstance(x, Mutex) for x in mutexes))
        assert semaphores is None or (isinstance(semaphores, (list, tuple)) and
            all(isinstance(x, Semaphore) for x in semaphores))
        assert binary_semaphores is None or (isinstance(binary_semaphores, (list, tuple)) and
            all(isinstance(x, BinarySemaphore) for x in binary_semaphores))
        assert composition is None or isinstance(composition, Composition)
        assert configuration is None or isinstance(configuration,
            Configuration)
        super(Component, self).__init__(location)
        self._name = name
        self._includes = list(includes or [])
        self._control = control
        self._hardware = hardware
        self._provides = list(provides or [])
        self._uses = list(uses or [])
        self._emits = list(emits or [])
        self._consumes = list(consumes or [])
        self._dataports = list(dataports or [])
        self._attributes = list(attributes or [])
        self._mutexes = list(mutexes or [])
        self._semaphores = list(semaphores or [])
        self._binary_semaphores = list(binary_semaphores or [])
        self._composition = composition
        self._configuration = configuration
        self.claim_children()

    def claim_children(self):
        [self.adopt(i) for i in self.includes]
        [self.adopt(p) for p in self.provides]
        [self.adopt(u) for u in self.uses]
        [self.adopt(e) for e in self.emits]
        [self.adopt(c) for c in self.consumes]
        [self.adopt(d) for d in self.dataports]
        [self.adopt(a) for a in self.attributes]
        [self.adopt(m) for m in self.mutexes]
        [self.adopt(s) for s in self.semaphores]
        [self.adopt(b) for b in self.binary_semaphores]
        if self.composition is not None:
            self.adopt(self.composition)
        if self.configuration is not None:
            self.adopt(self.configuration)

    @property
    def name(self):
        return self._name
    @name.setter
    def name(self, value):
        assert value is None or isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot change the name of a frozen component')
        self._name = value

    @property
    def includes(self):
        return self._includes
    @includes.setter
    def includes(self, value):
        assert isinstance(value, (list, tuple)) and \
            all(isinstance(x, Include) for x in value)
        if self.frozen:
            raise TypeError('you cannot change the includes of a frozen '
                'component')
        self._includes = value

    @property
    def control(self):
        return self._control
    @control.setter
    def control(self, value):
        assert isinstance(value, bool)
        if self.frozen:
            raise TypeError('you cannot change the control value of a frozen '
                'component')
        self._control = value

    @property
    def hardware(self):
        return self._hardware
    @hardware.setter
    def hardware(self, value):
        assert isinstance(value, bool)
        if self.frozen:
            raise TypeError('you cannot change the hardware value of a frozen '
                'component')
        self._hardware = value

    @property
    def provides(self):
        return self._provides
    @provides.setter
    def provides(self, value):
        assert isinstance(value, (list, tuple)) and \
            all(isinstance(x, Provides) for x in value)
        if self.frozen:
            raise TypeError('you cannot change the provides of a frozen '
                'component')
        self._provides = value

    @property
    def uses(self):
        return self._uses
    @uses.setter
    def uses(self, value):
        assert isinstance(value, (list, tuple)) and \
            all(isinstance(x, Uses) for x in value)
        if self.frozen:
            raise TypeError('you cannot change the uses of a frozen component')
        self._uses = value

    @property
    def emits(self):
        return self._emits
    @emits.setter
    def emits(self, value):
        assert isinstance(value, (list, tuple)) and \
            all(isinstance(x, Emits) for x in value)
        if self.frozen:
            raise TypeError('you cannot change the emits of a frozen '
                'component')
        self._emits = value

    @property
    def consumes(self):
        return self._consumes
    @consumes.setter
    def consumes(self, value):
        assert isinstance(value, (list, tuple)) and \
            all(isinstance(x, Consumes) for x in value)
        if self.frozen:
            raise TypeError('you cannot change the consumes of a frozen '
                'component')
        self._consumes = value

    @property
    def dataports(self):
        return self._dataports
    @dataports.setter
    def dataports(self, value):
        assert isinstance(value, (list, tuple)) and \
            all(isinstance(x, Dataport) for x in value)
        if self.frozen:
            raise TypeError('you cannot change the dataports of a frozen '
                'component')
        self._dataports = value

    @property
    def attributes(self):
        return self._attributes
    @attributes.setter
    def attributes(self, value):
        assert isinstance(value, (list, tuple)) and \
            all(isinstance(x, Attribute) for x in value)
        if self.frozen:
            raise TypeError('you cannot change the attributes of a frozen '
                'component')
        self._attributes = value

    @property
    def mutexes(self):
        return self._mutexes
    @mutexes.setter
    def mutexes(self, value):
        assert isinstance(value, (list, tuple)) and \
            all(isinstance(x, Mutex) for x in value)
        if self.frozen:
            raise TypeError('you cannot change the mutexes of a frozen '
                'component')
        self._mutexes = value

    @property
    def semaphores(self):
        return self._semaphores
    @semaphores.setter
    def semaphores(self, value):
        assert isinstance(value, (list, tuple)) and \
            all(isinstance(x, Semaphore) for x in value)
        if self.frozen:
            raise TypeError('you cannot change the semaphores of a frozen '
                'component')
        self._semaphores = value

    @property
    def binary_semaphores(self):
        return self._binary_semaphores
    @binary_semaphores.setter
    def binary_semaphores(self, value):
        assert isinstance(value, (list, tuple)) and \
            all(isinstance(x, BinarySemaphore) for x in value)
        if self.frozen:
            raise TypeError('you cannot change the binary_semaphores of a frozen '
                'component')
        self._binary_semaphores = value

    @property
    def composition(self):
        return self._composition
    @composition.setter
    def composition(self, value):
        assert value is None or isinstance(value, Composition)
        if self.frozen:
            raise TypeError('you cannot change the composition of a frozen '
                'component')
        self._composition = value

    @property
    def configuration(self):
        return self._configuration
    @configuration.setter
    def configuration(self, value):
        assert value is None or isinstance(value, Configuration)
        if self.frozen:
            raise TypeError('you cannot change the configuration of a frozen '
                'component')
        self._configuration = value

    def freeze(self):
        if self.frozen:
            return
        if self.control and self.hardware:
            raise ASTError('component %s is illegally defined as being both a '
                'control component and a hardware device' % self.name, self)
        if self.hardware:
            if len(self.mutexes) > 0:
                raise ASTError('component %s is illegally defined as a '
                    'hardware device that also has mutexes' % self.name, self)
            if len(self.semaphores) > 0:
                raise ASTError('component %s is illegally defined as a '
                    'hardware device that also has semaphores' % self.name,
                    self)
        self.includes = tuple(self.includes)
        self.provides = tuple(self.provides)
        self.uses = tuple(self.uses)
        self.emits = tuple(self.emits)
        self.consumes = tuple(self.consumes)
        self.dataports = tuple(self.dataports)
        self.attributes = tuple(self.attributes)
        self.mutexes = tuple(self.mutexes)
        self.semaphores = tuple(self.semaphores)
        super(Component, self).freeze()

class Interface(six.with_metaclass(abc.ABCMeta, ASTObject)):

    def __init__(self, location=None):
        super(Interface, self).__init__(location)

    def __str__(self):
        return self.name

class Provides(Interface):
    child_fields = ('type',)

    def __init__(self, type, name, location=None):
        assert isinstance(type, (Procedure, Reference))
        assert isinstance(name, six.string_types)
        super(Provides, self).__init__(location)
        self._type = type
        self._name = name

    @property
    def type(self):
        return self._type
    @type.setter
    def type(self, value):
        assert isinstance(value, (Procedure, Reference))
        if self.frozen:
            raise TypeError('you cannot change the type of a frozen provides')
        self._type = value

    @property
    def name(self):
        return self._name
    @name.setter
    def name(self, value):
        assert isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot change the name of a frozen provides')
        self._name = value

class Uses(Interface):
    child_fields = ('type',)

    def __init__(self, type, name, optional=False, location=None):
        assert isinstance(type, (Procedure, Reference))
        assert isinstance(name, six.string_types)
        assert isinstance(optional, bool)
        super(Uses, self).__init__(location)
        self._type = type
        self._name = name
        self._optional = optional

    @property
    def type(self):
        return self._type
    @type.setter
    def type(self, value):
        assert isinstance(value, (Procedure, Reference))
        if self.frozen:
            raise TypeError('you cannot set the type of a frozen uses')
        self._type = value

    @property
    def name(self):
        return self._name
    @name.setter
    def name(self, value):
        assert isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot set the name of a frozen uses')
        self._name = value

    @property
    def optional(self):
        return self._optional
    @optional.setter
    def optional(self, value):
        assert isinstance(value, bool)
        if self.frozen:
            raise TypeError('you cannot set optional of a frozen uses')
        self._optional = value

class Emits(Interface):
    def __init__(self, type, name, location=None):
        assert isinstance(type, six.string_types)
        assert isinstance(name, six.string_types)
        super(Emits, self).__init__(location)
        self._type = type
        self._name = name

    @property
    def type(self):
        return self._type
    @type.setter
    def type(self, value):
        assert isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot set the type of a frozen emits')
        self._type = value

    @property
    def name(self):
        return self._name
    @name.setter
    def name(self, value):
        assert isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot set the name of a frozen emits')
        self._name = value

class Consumes(Interface):
    def __init__(self, type, name, optional=False, location=None):
        assert isinstance(type, six.string_types)
        assert isinstance(name, six.string_types)
        assert isinstance(optional, bool)
        super(Consumes, self).__init__(location)
        self._type = type
        self._name = name
        self._optional = optional

    @property
    def type(self):
        return self._type
    @type.setter
    def type(self, value):
        assert isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot set the type of a frozen consumes')
        self._type = value

    @property
    def name(self):
        return self._name
    @name.setter
    def name(self, value):
        assert isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot set the name of a frozen consumes')
        self._name = value

    @property
    def optional(self):
        return self._optional
    @optional.setter
    def optional(self, value):
        assert isinstance(value, bool)
        if self.frozen:
            raise TypeError('you cannot set optional of a frozen consumes')
        self._optional = value

class Dataport(Interface):
    def __init__(self, type, name, optional=False, location=None):
        assert isinstance(type, six.string_types)
        assert isinstance(name, six.string_types)
        assert isinstance(optional, bool)
        super(Dataport, self).__init__(location)
        self._type = type
        self._name = name
        self._optional = optional

    @property
    def type(self):
        return self._type
    @type.setter
    def type(self, value):
        assert isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot set the type of a frozen dataport')
        self._type = value

    @property
    def name(self):
        return self._name
    @name.setter
    def name(self, value):
        assert isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot set the name of a frozen dataport')
        self._name = value

    @property
    def optional(self):
        return self._optional
    @optional.setter
    def optional(self, value):
        assert isinstance(value, bool)
        if self.frozen:
            raise TypeError('you cannot set optional of a frozen dataport')
        self._optional = value

class Mutex(ASTObject):
    def __init__(self, name, location=None):
        assert isinstance(name, six.string_types)
        super(Mutex, self).__init__(location)
        self._name = name

    @property
    def name(self):
        return self._name
    @name.setter
    def name(self, value):
        assert isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot set the name of a frozen mutex')
        self._name = value

class Semaphore(ASTObject):
    def __init__(self, name, location=None):
        assert isinstance(name, six.string_types)
        super(Semaphore, self).__init__(location)
        self._name = name

    @property
    def name(self):
        return self._name
    @name.setter
    def name(self, value):
        assert isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot set the name of a frozen '
                'semaphore')
        self._name = value

class BinarySemaphore(ASTObject):
    def __init__(self, name, location=None):
        assert isinstance(name, six.string_types)
        super(BinarySemaphore, self).__init__(location)
        self._name = name

    @property
    def name(self):
        return self._name
    @name.setter
    def name(self, value):
        assert isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot set the name of a frozen '
                'binary_semaphore')
        self._name = value

class Connector(ASTObject):
    def __init__(self, name=None, from_type=None, to_type=None,
            from_template=None, to_template=None, from_threads=1, to_threads=1,
            from_hardware=False, to_hardware=False, location=None):
        assert from_type is None or (isinstance(from_type, six.string_types) and \
            from_type in ('Event', 'Procedure', 'Dataport', 'Events',
            'Procedures', 'Dataports'))
        assert to_type is None or (isinstance(to_type, six.string_types) and \
            to_type in ('Event', 'Procedure', 'Dataport', 'Events',
            'Procedures', 'Dataports'))
        assert name is None or isinstance(name, six.string_types)
        assert from_template is None or isinstance(from_template,
            six.string_types)
        assert to_template is None or isinstance(to_template, six.string_types)
        assert isinstance(from_threads, six.integer_types) and from_threads >= 0
        assert isinstance(to_threads, six.integer_types) and to_threads >= 0
        assert isinstance(from_hardware, bool)
        assert isinstance(to_hardware, bool)
        super(Connector, self).__init__(location)
        TRANSLATION = {
            'Event':'Event',
            'Events':'Event',
            'Procedure':'Procedure',
            'Procedures':'Procedure',
            'Dataport':'Dataport',
            'Dataports':'Dataport',
        }
        self._name = name
        self._from_type = TRANSLATION.get(from_type)
        self._to_type = TRANSLATION.get(to_type)
        self._from_multiple = from_type in ('Events', 'Procedures', 'Dataports')
        self._to_multiple = to_type in ('Events', 'Procedures', 'Dataports')
        self._from_template = from_template
        self._to_template = to_template
        self._from_threads = from_threads
        self._to_threads = to_threads
        self._from_hardware = from_hardware
        self._to_hardware = to_hardware

    @property
    def name(self):
        return self._name
    @name.setter
    def name(self, value):
        assert value is None or isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot set the name of a frozen connector')
        self._name = value

    @property
    def from_type(self):
        return self._from_type
    @from_type.setter
    def from_type(self, value):
        assert isinstance(value, six.string_types) and \
            value in ('Dataport', 'Event', 'Procedure')
        if self.frozen:
            raise TypeError('you cannot set the from type of a frozen '
                'connector')
        self._from_type = value

    @property
    def to_type(self):
        return self._to_type
    @to_type.setter
    def to_type(self, value):
        assert isinstance(value, six.string_types) and \
            value in ('Dataport', 'Event', 'Procedure')
        if self.frozen:
            raise TypeError('you cannot set the to type of a frozen connector')
        self._to_type = value

    @property
    def from_multiple(self):
        return self._from_multiple
    @from_multiple.setter
    def from_multiple(self, value):
        assert isinstance(value, bool)
        if self.frozen:
            raise TypeError('you cannot set from multiple of a frozen '
                'connector')
        self._from_multiple = value

    @property
    def to_multiple(self):
        return self._to_multiple
    @to_multiple.setter
    def to_multiple(self, value):
        assert isinstance(value, bool)
        if self.frozen:
            raise TypeError('you cannot set to multiple of a frozen connector')
        self._to_multiple = value

    @property
    def from_template(self):
        return self._from_template
    @from_template.setter
    def from_template(self, value):
        assert value is None or isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot set from template of a frozen '
                'connector')
        self._from_template = value

    @property
    def to_template(self):
        return self._to_template
    @to_template.setter
    def to_template(self, value):
        assert value is None or isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot set to template of a frozen connector')
        self._to_template = value

    @property
    def from_threads(self):
        return self._from_threads
    @from_threads.setter
    def from_threads(self, value):
        assert isinstance(value, six.integer_types) and value >= 0
        if self.frozen:
            raise TypeError('you cannot set from threads of a frozen '
                'connector')
        self._from_threads = value

    @property
    def to_threads(self):
        return self._to_threads
    @to_threads.setter
    def to_threads(self, value):
        assert isinstance(value, six.integer_types) and value >= 0
        if self.frozen:
            raise TypeError('you cannot set to threads of a frozen connector')
        self._to_threads = value

    @property
    def from_hardware(self):
        return self._from_hardware
    @from_hardware.setter
    def from_hardware(self, value):
        assert isinstance(value, bool)
        if self.frozen:
            raise TypeError('you cannot set from hardware of a frozen '
                'connector')
        self._from_hardware = value

    @property
    def to_hardware(self):
        return self._to_hardware
    @to_hardware.setter
    def to_hardware(self, value):
        assert isinstance(value, bool)
        if self.frozen:
            raise TypeError('you cannot set to hardware of a frozen connector')
        self._to_hardware = value

class Group(MapLike):
    child_fields = ('instances',)

    def __init__(self, name=None, instances=None, location=None):
        assert name is None or isinstance(name, six.string_types)
        assert instances is None or (isinstance(instances, (list, tuple)) and
            all(isinstance(x, Instance) for x in instances))
        super(Group, self).__init__(location)
        self._name = name
        self._instances = list(instances or [])
        self.claim_children()

    @property
    def name(self):
        return self._name
    @name.setter
    def name(self, value):
        assert value is None or isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot set the name of a frozen group')
        self._name = value

    @property
    def instances(self):
        return self._instances
    @instances.setter
    def instances(self, value):
        assert isinstance(value, (list, tuple)) and \
            all(isinstance(x, Instance) for x in value)
        if self.frozen:
            raise TypeError('you cannot set the instances of a frozen group')
        self._instances = value

    def claim_children(self):
        [self.adopt(i) for i in self.instances]

class Procedure(MapLike):
    child_fields = ('includes', 'methods', 'attributes')

    def __init__(self, name=None, includes=None, methods=None, attributes=None, location=None):
        assert name is None or isinstance(name, six.string_types)
        assert includes is None or (isinstance(includes, (list, tuple)) and
            all(isinstance(x, Include) for x in includes))
        assert methods is None or (isinstance(methods, (list, tuple)) and
            all(isinstance(x, Method) for x in methods))
        assert attributes is None or (isinstance(attributes, (list, tuple)) and
            all(isinstance(x, Attribute) for x in attributes))
        super(Procedure, self).__init__(location)
        self._name = name
        self._includes = list(includes or [])
        self._methods = list(methods or [])
        self._attributes = list(attributes or [])
        self.claim_children()

    @property
    def name(self):
        return self._name
    @name.setter
    def name(self, value):
        assert value is None or isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot set the name of a frozen procedure')
        self._name = value

    @property
    def includes(self):
        return self._includes
    @includes.setter
    def includes(self, value):
        assert isinstance(value, (list, tuple)) and \
            all(isinstance(x, Include) for x in value)
        if self.frozen:
            raise TypeError('you cannot set the includes of a frozen '
                'procedure')
        self._includes = value

    @property
    def methods(self):
        return self._methods
    @methods.setter
    def methods(self, value):
        assert isinstance(value, (list, tuple)) and \
            all(isinstance(x, Method) for x in value)
        if self.frozen:
            raise TypeError('you cannot set the methods of a frozen procedure')
        self._methods = value

    @property
    def attributes(self):
        return self._attributes
    @attributes.setter
    def attributes(self, value):
        assert isinstance(value, (list, tuple)) and \
            all(isinstance(x, Attribute) for x in value)
        if self.frozen:
            raise TypeError('you cannot set the attributes of a frozen '
                'procedure')
        self._attributes = value

    def claim_children(self):
        [self.adopt(i) for i in self.includes]
        [self.adopt(m) for m in self.methods]
        [self.adopt(a) for a in self.attributes]

class Method(ASTObject):
    child_fields = ('parameters',)

    def __init__(self, name, return_type, parameters, location=None):
        assert isinstance(name, six.string_types)
        assert return_type is None or isinstance(return_type, six.string_types)
        assert isinstance(parameters, (list, tuple)) and \
            all(isinstance(x, Parameter) for x in parameters)
        super(Method, self).__init__(location)
        self._name = name
        self._return_type = return_type
        self._parameters = list(parameters)
        self.claim_children()

    @property
    def name(self):
        return self._name
    @name.setter
    def name(self, value):
        assert isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot set the \'name\' field of a frozen '
                'object')
        self._name = value

    @property
    def return_type(self):
        return self._return_type
    @return_type.setter
    def return_type(self, value):
        assert value is None or isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot set the \'return_type\' field of a '
                'frozen object')
        self._return_type = value

    @property
    def parameters(self):
        return self._parameters
    @parameters.setter
    def parameters(self, value):
        assert isinstance(value, (list, tuple)) and \
            all(isinstance(x, Parameter) for x in value)
        if self.frozen:
            raise TypeError('you cannot set the \'parameters\' field of a '
                'frozen object')
        self._parameters = value

    def claim_children(self):
        [self.adopt(p) for p in self.parameters]

    def freeze(self):
        if self.frozen:
            return
        if self.name in C_KEYWORDS:
            raise ASTError('method name \'%s\' clashes with a C keyword' %
                self.name, self)
        params = set()
        for p in self.parameters:
            if p.name in params:
                raise ASTError('duplicate parameter name \'%s\' in method '
                    '\'%s\'' % (p.name, self.name), self)
            params.add(p.name)
        self.parameters = tuple(self.parameters)
        super(Method, self).freeze()

class Attribute(ASTObject):
    def __init__(self, type, name, array=False, default=None, location=None):
        assert isinstance(type, (six.string_types, Reference, Struct))
        assert isinstance(name, six.string_types)
        assert isinstance(array, bool)
        super(Attribute, self).__init__(location)
        self._name = name
        self._type = type
        self._default = default
        self._array = array
        if isinstance(type, (Reference, Struct)):
            self.child_fields = ('type',)

    @property
    def name(self):
        return self._name
    @name.setter
    def name(self, value):
        assert isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot set the \'name\' field of a frozen '
                'object')
        self._name = value

    @property
    def type(self):
        return self._type
    @type.setter
    def type(self, value):
        assert isinstance(value, (six.string_types, Reference, Struct))
        if self.frozen:
            raise TypeError('you cannot set the \'type\' field of a frozen '
                'object')
        self._type = value
        if isinstance(value, (Reference, Struct)):
            self.child_fields = ('type',)
        else:
            self.child_fields = ()

    @property
    def array(self):
        return self._array
    @array.setter
    def array(self, value):
        assert isinstance(value, bool)
        if self.frozen:
            raise TypeError('you cannot set the \'array\' field of a frozen '
                'object')
        self._array = value

    @property
    def default(self):
        return self._default
    @default.setter
    def default(self, value):
        assert value is None or isinstance(value, (numbers.Number, list, dict)
            + six.string_types)
        if self.frozen:
            raise TypeError('you cannot set the \'default\' field of a frozen '
                'object')
        self._default = value

    def freeze(self):
        if self.frozen:
            return
        if self.name in C_KEYWORDS:
            raise ASTError('attribute name \'%s\' clashes with a C keyword' %
                self.name, self)
        super(Attribute, self).freeze()

class Parameter(ASTObject):
    def __init__(self, name, direction, type, array=False, location=None):
        assert isinstance(name, six.string_types)
        assert isinstance(direction, six.string_types) and \
            direction in ('in', 'inout', 'out', 'refin')
        assert isinstance(type, six.string_types)
        assert isinstance(array, bool)
        super(Parameter, self).__init__(location)
        self._name = name
        self._direction = direction
        self._type = type
        self._array = array

    @property
    def name(self):
        return self._name
    @name.setter
    def name(self, value):
        assert isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot set the \'name\' field of a frozen '
                'object')
        self._name = value

    @property
    def direction(self):
        return self._direction
    @direction.setter
    def direction(self, value):
        assert isinstance(value, six.string_types) and \
            value in ('in', 'inout', 'out', 'refin')
        if self.frozen:
            raise TypeError('you cannot set the \'direction\' field of a '
                'frozen object')
        self._direction = value

    @property
    def type(self):
        return self._type
    @type.setter
    def type(self, value):
        assert isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot set the \'type\' field of a frozen '
                'object')
        self._type = value

    @property
    def array(self):
        return self._array
    @array.setter
    def array(self, value):
        assert isinstance(value, bool)
        if self.frozen:
            raise TypeError('you cannot set the \'array\' field of a frozen '
                'object')
        self._array = value

    def freeze(self):
        if self.frozen:
            return
        if self.name in C_KEYWORDS:
            raise ASTError('parameter name \'%s\' clashes with a C keyword' %
                self.name, self)
        super(Parameter, self).freeze()

class ConnectionEnd(ASTObject):
    child_fields = ('instance', 'interface')

    def __init__(self, end, instance, interface, location=None):
        assert isinstance(end, six.string_types) and end in ('from', 'to')
        assert instance is None or isinstance(instance, (Instance, Reference))
        assert isinstance(interface, (Interface, Reference))
        super(ConnectionEnd, self).__init__(location)
        self._end = end
        self._instance = instance
        self._interface = interface

    @property
    def end(self):
        return self._end
    @end.setter
    def end(self, value):
        assert isinstance(value, six.string_types) and value in ('from', 'to')
        if self.frozen:
            raise TypeError('you cannot set the \'end\' field of a frozen '
                'object')
        self._end = value

    @property
    def instance(self):
        return self._instance
    @instance.setter
    def instance(self, value):
        assert value is None or isinstance(value, (Instance, Reference))
        if self.frozen:
            raise TypeError('you cannot set the \'instance\' field of a '
                'frozen object')
        self._instance = value

    @property
    def interface(self):
        return self._interface
    @interface.setter
    def interface(self, value):
        assert isinstance(value, (Interface, Reference))
        if self.frozen:
            raise TypeError('you cannot set the \'interface\' field of a '
                'frozen object')
        self._interface = value

    # Shorthand that can replace the use of a very commonly repeated
    # condition in the templates.
    #
    # This tests to see if the entity might block.
    def might_block(self):
        return len(self.instance.type.provides + self.instance.type.uses \
            + self.instance.type.consumes \
            + self.instance.type.mutexes + self.instance.type.semaphores) > 1

    def label(self):
        return self.parent.label()

    def get_end_type(self):
        '''
        If the instance is none but the composition that this connection
        is in is inside a component, then the type of that end is the top
        component.
        '''
        if self.instance is not None:
            return self.instance.type
        # self.parent is a connection
        # self.parent.parent is a composition
        # self.parent.parent.parent is either an assembly or Component
        # The parser shouldn't get to this point if the parent.parent.parent
        # isn't a Component
        assert isinstance(self.parent.parent.parent, Component)
        return self.parent.parent.parent

    def __str__(self):
        return "%s.%s" % (str(self.instance), str(self.interface))

class Export(ASTObject):
    child_fields = ('source_instance', 'source_interface', 'destination')

    def __init__(self, source_instance, source_interface, destination,
            location=None):
        assert isinstance(source_instance, (Instance, Reference))
        assert isinstance(source_interface, (Interface, Reference))
        assert isinstance(destination, (Interface, Reference))
        super(Export, self).__init__(location)
        self._source_instance = source_instance
        self._source_interface = source_interface
        self._destination = destination

    @property
    def source_instance(self):
        return self._source_instance
    @source_instance.setter
    def source_instance(self, value):
        assert isinstance(value, (Instance, Reference))
        if self.frozen:
            raise TypeError('you cannot set the \'source_instance\' field of '
                'a frozen object')
        self._source_instance = value

    @property
    def source_interface(self):
        return self._source_interface
    @source_interface.setter
    def source_interface(self, value):
        assert isinstance(value, (Interface, Reference))
        if self.frozen:
            raise TypeError('you cannot set the \'source_interface\' field of '
                'a frozen object')
        self._source_interface = value

    @property
    def destination(self):
        return self._destination
    @destination.setter
    def destination(self, value):
        assert isinstance(value, (Interface, Reference))
        if self.frozen:
            raise TypeError('you cannot set the \'destination\' field of a '
                'frozen object')
        self._destination = value

class AttributeReference(ASTObject):
    def __init__(self, reference, location=None):
        assert isinstance(reference, six.string_types)
        super(AttributeReference, self).__init__(location)
        self._reference = reference

    @property
    def reference(self):
        return self._reference
    @reference.setter
    def reference(self, value):
        assert isinstance(value, six.string_types)
        if self.frozen:
            raise TypeError('you cannot set the \'reference\' field of a '
                'frozen object')
        self._reference = value
