#!/usr/bin/env python
# -*- coding: utf-8 -*-

import six

from PyQt5 import QtGui, QtWidgets
from camkes.ast import *


# TODO: subclass Qt
class InstanceWidget(QtWidgets.QFrame):

    @property
    def instance_object(self):
        return self._instance_object

    @instance_object.setter
    def instance_object(self, value):
        assert isinstance(value, Instance)
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
        # Model
        self._instance_object = instance_object
        self._instance_name = instance_object.name

        # GUI
        layout = QtWidgets.QVBoxLayout()



        component_type = self.instance_object.type
        assert isinstance(component_type, Component)

        string = instance_object.name + ": " + component_type.name
        new_label = QtWidgets.QLabel(string)
        # self.setFrameStyle(QtWidgets.QFrame.Panel)
        #new_label.setLineWidth(2)
        layout.addWidget(new_label)

        if component_type.control:
            layout.addWidget(QtWidgets.QLabel("control;"))

        if component_type.hardware:
            layout.addWidget(QtWidgets.QLabel("hardware;"))

        self.setLayout(layout)
