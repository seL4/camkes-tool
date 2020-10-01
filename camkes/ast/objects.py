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
from camkes.internal.isinstancefallback import isinstance_fallback
import abc
import collections
import itertools
import numbers
import six
import logging
from types import LambdaType


def types_compatible(value, attribute):
    type = attribute.type
    assert isinstance(type, (six.string_types, Struct))
    if attribute.array is True:
        assert isinstance(value, (tuple, list))
        values = value
    else:
        values = (value,)
    for value in values:
        if isinstance(type, six.string_types):
            if (isinstance(value, six.integer_types) and type not in ('int', 'uint64_t', 'int64_t')):
                return (False, "For \"%s\": required type is \"int\", but type is \"%s\"" % (str(value), type))
            if (isinstance(value, float) and type not in ('double', 'float')):
                return (False, "For \"%s\": required type is \"float\", but type is \"%s\"" % (str(value), type))
            if (isinstance(value, six.string_types) and type != 'string'):
                return (False, "For \"%s\": required type is \"string\", but type is \"%s\"" % (str(value), type))
            if (isinstance(value, list) and type != 'list'):
                return (False, "For \"%s\": required type is \"list\", but type is \"%s\"" % (str(value), type))
            if ((isinstance(value, dict) and type != 'dict')):
                return (False, "For \"%s\": required type is \"dict\", but type is \"%s\"" % (str(value), type))

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
                    logging.warn("Attributes: \"%s\" are missing from assignment." % new_missing)

            extra_attrs = list(set(value.keys()) - attr_names)
            if len(extra_attrs) != 0:
                logging.warn("Attributes: \"%s\" do not exist in \"%s\" definition." %
                             (extra_attrs, type.name))

            for x in type.attributes:
                (compat, error_str) = types_compatible(value[x.name], x)
                if not compat:
                    return (False, error_str)
    return (True, "")


def ast_property(name, types):
    '''Creates custom getter and setter functions for an AST property.
       Typechecks and raises exception if frozen
    '''
    assert isinstance(name, six.string_types)

    def prop_class_decorator(cls):
        prop_name = "_%s" % name
        (fget, fset, fdel) = (None, None, None)
        old_prop = getattr(cls, name, None)
        if old_prop is not None:
            (fget, fset, fdel) = (old_prop.fget, old_prop.fset, old_prop.fdel)

        def get_prop(self):
            if fget:
                # Call a getter function if it already exists.
                return fget(self)
            return getattr(self, prop_name)

        def set_prop(self, value):
            if isinstance(types, LambdaType):
                assert types(value)
            else:
                assert isinstance(value, types)
            if self.frozen:
                raise TypeError('Tried to change {0} on object {1} to value {2} but object is frozen' %
                                (name, self.__class__.__name__, value))
            if fset:
                # Call the setter if it already exists.
                fset(self, value)
                return
            setattr(self, prop_name, value)

        prop = property(get_prop, set_prop, fdel)
        setattr(cls, name, prop)
        return cls
    return prop_class_decorator


@ast_property("source", six.string_types)
@ast_property("relative", bool)
class Include(ASTObject):
    def __init__(self, source, relative=True, location=None):
        super(Include, self).__init__(location)
        self.source = source
        self.relative = relative


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


@ast_property("name", lambda x: x is None or isinstance(x, six.string_types))
@ast_property("composition", lambda x: isinstance(x, Reference) or isinstance_fallback(x, "Composition"))
@ast_property("configuration", lambda x: isinstance(x, Reference) or isinstance_fallback(x, "Configuration"))
class Assembly(ASTObject):
    child_fields = ('composition', 'configuration')

    def __init__(self, name=None, composition=None, configuration=None, location=None):
        super(Assembly, self).__init__(location)
        self.name = name
        if composition is not None:
            self.composition = composition
        if configuration is None:
            configuration = Configuration()
        self.configuration = configuration
        self.claim_children()

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


@ast_property("name", lambda x: x is None or isinstance(x, six.string_types))
@ast_property("instances", lambda i: isinstance(i, (list, tuple)) and
              all(isinstance(x, (Reference)) or isinstance_fallback(x, "Instance") for x in i))
@ast_property("connections", lambda c: isinstance(c, (list, tuple)) and
              all(isinstance(x, (Reference)) or isinstance_fallback(x, "Connection") for x in c))
@ast_property("groups", lambda g: isinstance(g, (list, tuple)) and
              all(isinstance(x, (Reference)) or isinstance_fallback(x, "Group") for x in g))
@ast_property("exports", lambda e: isinstance(e, (list, tuple)) and
              all(isinstance(x, (Reference)) or isinstance_fallback(x, "Export") for x in e))
class Composition(MapLike):
    # Note that the ordering of these child fields is important as members of
    # `connections` and `exports` may reference members of `instances` and/or
    # `groups`, so both of the latter need to be seen by scoping resolution
    # before the former.
    child_fields = ('instances', 'groups', 'connections', 'exports')

    def __init__(self, name=None, instances=None, connections=None,
                 groups=None, exports=None, location=None):
        super(Composition, self).__init__(location)
        self.name = name
        self.instances = list(instances or [])
        self.connections = list(connections or [])
        self.groups = list(groups or [])
        self.exports = list(exports or [])
        self.claim_children()

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


@ast_property("name", lambda x: x is None or isinstance(x, six.string_types))
@ast_property("settings", (list, tuple))
class Configuration(MapLike):
    child_fields = ('settings',)

    def __init__(self, name=None, settings=None, location=None):
        super(Configuration, self).__init__(location)
        self.name = name
        self.settings = list(settings or [])
        self.settings_dict = {}
        self.claim_children()

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


@ast_property("type", lambda x: isinstance(x, (Reference)) or isinstance_fallback(x, "Component"))
@ast_property("name", six.string_types)
@ast_property("address_space", six.string_types)
class Instance(ASTObject):
    child_fields = ('type',)

    def __init__(self, type, name, location=None):
        super(Instance, self).__init__(location)
        self.type = type
        self.name = name
        self.address_space = name

    def label(self):
        return self.name

    @property
    def instance(self):
        return self

    def __str__(self):
        return self.name


@ast_property("type", lambda x: isinstance(x, (Reference)) or isinstance_fallback(x, "Connector"))
@ast_property("name", six.string_types)
@ast_property("from_ends", (list, tuple))
@ast_property("to_ends", (list, tuple))
class Connection(ASTObject):
    child_fields = ('from_ends', 'to_ends', 'type')

    def __init__(self, connection_type, name, from_ends, to_ends, location=None):
        super(Connection, self).__init__(location)
        self.type = connection_type
        self.name = name
        self.from_ends = from_ends
        self.to_ends = to_ends
        self.claim_children()

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
        interface_checking_attrib = self.type.get_attribute("disable_interface_type_checking")
        if len(types) > 1 and (not interface_checking_attrib or not interface_checking_attrib.default):
            raise ASTError('multiple conflicting types for the '
                           'interfaces of connection \'%s\': %s' % (self.name,
                                                                    ', '.join([(t.name if hasattr(t, 'name') else type(t).__name__) for t in types])), self)
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


@ast_property("instance", six.string_types)
@ast_property("attribute", six.string_types)
@ast_property("value", lambda x: isinstance(x, (numbers.Number, list, tuple, frozendict, dict, six.string_types)) or isinstance_fallback(x, "AttributeReference")
              or isinstance_fallback(x, "QueryObject"))
class Setting(ASTObject):
    def __init__(self, instance, attribute, value, location=None):
        super(Setting, self).__init__(location)
        self.instance = instance
        self.attribute = attribute
        self.value = value
        if isinstance(value, Reference):
            self.child_fields = ('value',)

    # This property is wrapped by the ast_property decorator which adds on type checking and the frozen check
    @property
    def value(self):
        return self._value

    @value.setter
    def value(self, value):
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


@ast_property("name", six.string_types)
@ast_property("attributes", lambda a: isinstance(a, (list, tuple)) and
              all(isinstance_fallback(x, "Attribute") for x in a))
class Struct(ASTObject):
    child_fields = ('attributes',)
    anon_struct_count = 0

    def __init__(self, name=None, attributes=None, location=None):
        super(Struct, self).__init__(location)

        if name is None:
            # Generate a struct name as none was provided.
            name = "camkes_anon_struct_%d" % Struct.anon_struct_count
            Struct.anon_struct_count = Struct.anon_struct_count + 1
        self.name = name
        self.attributes = list(attributes or [])

    def __str__(self):
        return self.name

    def freeze(self):
        if self.frozen:
            return
        self.attributes = tuple(self.attributes)
        super(Struct, self).freeze()


@ast_property("name", lambda x: x is None or isinstance(x, six.string_types))
@ast_property("control", bool)
@ast_property("hardware", bool)
@ast_property("includes", lambda i: isinstance(i, (list, tuple)) and
              all(isinstance_fallback(x, "Include") for x in i))
@ast_property("provides", lambda p: isinstance(p, (list, tuple)) and
              all(isinstance_fallback(x, "Provides") for x in p))
@ast_property("uses", lambda u: isinstance(u, (list, tuple)) and
              all(isinstance_fallback(x, "Uses") for x in u))
@ast_property("emits", lambda e: isinstance(e, (list, tuple)) and
              all(isinstance_fallback(x, "Emits") for x in e))
@ast_property("consumes", lambda c: isinstance(c, (list, tuple)) and
              all(isinstance_fallback(x, "Consumes") for x in c))
@ast_property("dataports", lambda d: isinstance(d, (list, tuple)) and
              all(isinstance_fallback(x, "Dataport") for x in d))
@ast_property("attributes", lambda a: isinstance(a, (list, tuple)) and
              all(isinstance_fallback(x, "Attribute") for x in a))
@ast_property("mutexes", lambda m: isinstance(m, (list, tuple)) and
              all(isinstance_fallback(x, "Mutex") for x in m))
@ast_property("semaphores", lambda s: isinstance(s, (list, tuple)) and
              all(isinstance_fallback(x, "Semaphore") for x in s))
@ast_property("binary_semaphores", lambda b: isinstance(b, (list, tuple)) and
              all(isinstance_fallback(x, "BinarySemaphore") for x in b))
@ast_property("composition", Composition)
@ast_property("configuration", Configuration)
class Component(MapLike):
    child_fields = ('attributes', 'includes', 'provides', 'uses', 'emits',
                    'consumes', 'dataports', 'mutexes', 'semaphores', 'binary_semaphores', 'composition',
                    'configuration')

    def __init__(self, name=None, includes=None, control=False, hardware=False,
                 provides=None, uses=None, emits=None, consumes=None, dataports=None,
                 attributes=None, mutexes=None, semaphores=None, binary_semaphores=None, composition=None,
                 configuration=None, location=None):
        super(Component, self).__init__(location)
        self.name = name
        self.includes = list(includes or [])
        self.control = control
        self.hardware = hardware
        self.provides = list(provides or [])
        self.uses = list(uses or [])
        self.emits = list(emits or [])
        self.consumes = list(consumes or [])
        self.dataports = list(dataports or [])
        self.attributes = list(attributes or [])
        self.mutexes = list(mutexes or [])
        self.semaphores = list(semaphores or [])
        self.binary_semaphores = list(binary_semaphores or [])
        if composition is not None:
            self.composition = composition
        else:
            self._composition = None
        if configuration is not None:
            self.configuration = configuration
        else:
            self._configuration = None
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

    def interface_is_exported(self, interface):
        '''Check whether the given interface is an `export` endpoint.
           This is used to remove virtual interfaces in the generated Isabelle model.'''
        return (self.composition is not None and
                any(interface == ex.destination.name for ex in self.composition.exports))


class Interface(six.with_metaclass(abc.ABCMeta, ASTObject)):

    def __init__(self, location=None):
        super(Interface, self).__init__(location)

    def __str__(self):
        return self.name


@ast_property("name", six.string_types)
@ast_property("type", lambda x: isinstance(x, (Reference)) or isinstance_fallback(x, "Procedure"))
class Provides(Interface):
    child_fields = ('type',)

    def __init__(self, type, name, location=None):
        super(Provides, self).__init__(location)
        self.type = type
        self.name = name


@ast_property("type", lambda x: isinstance(x, (Reference)) or isinstance_fallback(x, "Procedure"))
@ast_property("name", six.string_types)
@ast_property("optional", bool)
class Uses(Interface):
    child_fields = ('type',)

    def __init__(self, type, name, optional=False, location=None):
        super(Uses, self).__init__(location)
        self.type = type
        self.name = name
        self.optional = optional


@ast_property("type", six.string_types)
@ast_property("name", six.string_types)
class Emits(Interface):
    def __init__(self, type, name, location=None):
        super(Emits, self).__init__(location)
        self.type = type
        self.name = name


@ast_property("type", six.string_types)
@ast_property("name", six.string_types)
@ast_property("optional", bool)
class Consumes(Interface):
    def __init__(self, type, name, optional=False, location=None):
        super(Consumes, self).__init__(location)
        self.type = type
        self.name = name
        self.optional = optional


@ast_property("type", six.string_types)
@ast_property("name", six.string_types)
@ast_property("optional", bool)
class Dataport(Interface):
    def __init__(self, type, name, optional=False, location=None):
        super(Dataport, self).__init__(location)
        self.type = type
        self.name = name
        self.optional = optional


@ast_property("name", six.string_types)
class Mutex(ASTObject):
    def __init__(self, name, location=None):
        super(Mutex, self).__init__(location)
        self.name = name


@ast_property("name", six.string_types)
class Semaphore(ASTObject):
    def __init__(self, name, location=None):
        super(Semaphore, self).__init__(location)
        self.name = name


@ast_property("name", six.string_types)
class BinarySemaphore(ASTObject):
    def __init__(self, name, location=None):
        super(BinarySemaphore, self).__init__(location)
        self.name = name


@ast_property("name", lambda x: x is None or isinstance(x, six.string_types))
@ast_property("from_type", lambda x: isinstance(x, six.string_types) and
              x in ('Dataport', 'Event', 'Procedure'))
@ast_property("to_type", lambda x: isinstance(x, six.string_types) and
              x in ('Dataport', 'Event', 'Procedure'))
@ast_property("from_multiple", bool)
@ast_property("to_multiple", bool)
@ast_property("from_threads", lambda x: isinstance(x, six.integer_types) and x >= 0)
@ast_property("to_threads", lambda x: isinstance(x, six.integer_types) and x >= 0)
@ast_property("from_hardware", bool)
@ast_property("to_hardware", bool)
@ast_property("attributes", lambda x: isinstance(x, (list, tuple)) and
              all(isinstance_fallback(y, "Attribute") for y in value))
class Connector(ASTObject):
    def __init__(self, name=None, from_type=None, to_type=None,
                 from_threads=1, to_threads=1,
                 from_hardware=False, to_hardware=False, attributes=None, location=None):
        super(Connector, self).__init__(location)
        TRANSLATION = {
            'Event': 'Event',
            'Events': 'Event',
            'Procedure': 'Procedure',
            'Procedures': 'Procedure',
            'Dataport': 'Dataport',
            'Dataports': 'Dataport',
        }
        self.name = name
        if from_type:
            self.from_type = TRANSLATION.get(from_type)
        else:
            self._from_type = None
        if to_type:
            self.to_type = TRANSLATION.get(to_type)
        else:
            self._to_type = None
        self.from_multiple = from_type in ('Events', 'Procedures', 'Dataports')
        self.to_multiple = to_type in ('Events', 'Procedures', 'Dataports')
        self.from_threads = from_threads
        self.to_threads = to_threads
        self.from_hardware = from_hardware
        self.to_hardware = to_hardware
        self._attributes = attributes

    def get_attribute(self, attribute_name):
        for attrib in self.attributes:
            if attrib.name == attribute_name:
                return attrib
        return None


@ast_property("name", lambda x: x is None or isinstance(x, six.string_types))
@ast_property("instances", lambda i: isinstance(i, (list, tuple)) and
              all(isinstance(x, Instance) for x in i))
class Group(MapLike):
    child_fields = ('instances',)

    def __init__(self, name=None, instances=None, location=None):
        super(Group, self).__init__(location)
        self.name = name
        self.instances = list(instances or [])
        self.claim_children()

    def claim_children(self):
        [self.adopt(i) for i in self.instances]


@ast_property("name", lambda x: x is None or (isinstance(x, six.string_types)))
@ast_property("includes", lambda i: isinstance(i, (list, tuple)) and
              all(isinstance(x, Include) for x in i))
@ast_property("methods", lambda m: isinstance(m, (list, tuple)) and
              all(isinstance(x, Method) for x in m))
@ast_property("attributes", lambda a: isinstance(a, (list, tuple)) and
              all(isinstance(x, Attribute) for x in a))
class Procedure(MapLike):
    child_fields = ('includes', 'methods', 'attributes')

    def __init__(self, name=None, includes=None, methods=None, attributes=None, location=None):
        super(Procedure, self).__init__(location)
        self.name = name
        self.includes = list(includes or [])
        self.methods = list(methods or [])
        self.attributes = list(attributes or [])
        self.claim_children()

    def claim_children(self):
        [self.adopt(i) for i in self.includes]
        [self.adopt(m) for m in self.methods]
        [self.adopt(a) for a in self.attributes]


@ast_property("name", six.string_types)
@ast_property("return_type", lambda x: x is None or isinstance(x, six.string_types))
@ast_property("parameters", lambda p: isinstance(p, (list, tuple)) and
              all(isinstance(x, Parameter) for x in p))
class Method(ASTObject):
    child_fields = ('parameters',)

    def __init__(self, name, return_type, parameters, location=None):
        super(Method, self).__init__(location)
        self.name = name
        self.return_type = return_type
        self.parameters = list(parameters)
        self.claim_children()

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


@ast_property("type", (six.string_types, Reference, Struct))
@ast_property("name", six.string_types)
@ast_property("array", bool)
@ast_property("default", lambda x: x is None or isinstance(x, (numbers.Number, list, dict, six.string_types)))
class Attribute(ASTObject):
    def __init__(self, type, name, array=False, default=None, location=None):
        super(Attribute, self).__init__(location)
        self.name = name
        self.type = type
        self.default = default
        self.array = array
        if isinstance(type, (Reference, Struct)):
            self.child_fields = ('type',)

    # Type checking and frozen checks are done by ast_property delegate
    @property
    def type(self):
        return self._type

    @type.setter
    def type(self, value):
        self._type = value
        if isinstance(value, (Reference, Struct)):
            self.child_fields = ('type',)
        else:
            self.child_fields = ()

    def freeze(self):
        if self.frozen:
            return
        if self.name in C_KEYWORDS:
            raise ASTError('attribute name \'%s\' clashes with a C keyword' %
                           self.name, self)
        super(Attribute, self).freeze()


@ast_property("name", six.string_types)
@ast_property("direction", lambda x: isinstance(x, six.string_types) and x in ('in', 'inout', 'out', 'refin'))
@ast_property("type", six.string_types)
@ast_property("array", bool)
class Parameter(ASTObject):
    def __init__(self, name, direction, type, array=False, location=None):
        super(Parameter, self).__init__(location)
        self.name = name
        self.direction = direction
        self.type = type
        self.array = array

    def freeze(self):
        if self.frozen:
            return
        if self.name in C_KEYWORDS:
            raise ASTError('parameter name \'%s\' clashes with a C keyword' %
                           self.name, self)
        super(Parameter, self).freeze()


@ast_property("end", lambda x: isinstance(x, six.string_types) and x in ('from', 'to'))
@ast_property("instance", lambda x: x is None or isinstance(x, (Instance, Reference)))
@ast_property("interface", (Interface, Reference))
class ConnectionEnd(ASTObject):
    child_fields = ('instance', 'interface')

    def __init__(self, end, instance, interface, location=None):
        super(ConnectionEnd, self).__init__(location)
        self.end = end
        self.instance = instance
        self.interface = interface

    # Shorthand that can replace the use of a very commonly repeated
    # condition in the templates.
    #
    # This tests to see if the entity might block.
    def might_block(self):
        return len(self.instance.type.provides + self.instance.type.uses
                   + self.instance.type.consumes
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


@ast_property("source_instance", (Instance, Reference))
@ast_property("source_interface", (Interface, Reference))
@ast_property("destination", (Interface, Reference))
class Export(ASTObject):
    child_fields = ('source_instance', 'source_interface', 'destination')

    def __init__(self, source_instance, source_interface, destination,
                 location=None):
        super(Export, self).__init__(location)
        self.source_instance = source_instance
        self.source_interface = source_interface
        self.destination = destination


@ast_property("reference", six.string_types)
@ast_property("dict_lookup", lambda x: x is None or isinstance_fallback(x, "DictLookup"))
class AttributeReference(ASTObject):
    def __init__(self, reference, dict_lookup, location=None):
        super(AttributeReference, self).__init__(location)
        self.reference = reference
        self.dict_lookup = dict_lookup


@ast_property("lookup", list)
class DictLookup(ASTObject):
    def __init__(self, lookup, location):
        super(DictLookup, self).__init__(location)
        self.lookup = lookup


@ast_property("type", six.string_types)
@ast_property("args", lambda i: isinstance(i, list) and
              all(isinstance(x, dict) for x in i))
@ast_property("dict_lookup", lambda x: x is None or isinstance(x, DictLookup))
class QueryObject(ASTObject):
    def __init__(self, query_name, query_args, dict_lookup, location):
        super(QueryObject, self).__init__(location)
        self.type = query_name  # the name of the query
        self.args = query_args  # the arguments passed to the query
        self.dict_lookup = dict_lookup
