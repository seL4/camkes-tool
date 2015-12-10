#!/usr/bin/env python
# -*- coding: utf-8 -*-

from gi.repository import Gtk
from camkes.ast.objects import *


class InstanceWidget(Gtk.Bin):

    @property
    def instance_object(self):
        return self._instance_object

    @instance_object.setter
    def instance_object(self, value):
        assert issubclass(value.__class__, Instance) or isinstance(value, Instance)
        self._instance_object = value

    @property
    def instance_name(self):
        if self._instance_name is None:
            raise Exception # TODO make subclass of exception, catch and show a dialog
        return self._instance_name

    @instance_name.setter
    def instance_name(self, value):
        assert isinstance(value, six.string_types)
        self._instance_name = value

    def __init__(self, instance_object):
        super(InstanceWidget, self).__init__()

        assert issubclass(instance_object.__class__, Instance) or isinstance(instance_object, Instance)
        self._instance_object = instance_object
        self._instance_name = instance_object.name

        new_widget_builder = Gtk.Builder()
        new_widget_builder.add_from_file("../View/gladeASTTest.builder")

        instance_label = new_widget_builder.get_object("instance_name_label")
        assert isinstance(instance_label, Gtk.Label)
        instance_label.set_text(instance_object.name)

        component_type_label = new_widget_builder.get_object("component_type")
        assert isinstance(component_type_label, Gtk.Label)
        component_type_label.set_text(instance_object.type.name)

        new_widget_frame = new_widget_builder.get_object("Instance_frame")

        self.add(new_widget_frame)

    # What a hack (hacky because only works on this function). TODO: see if better way of doing this
    def get_preferred_size(self):
        return self.get_child().get_preferred_size()