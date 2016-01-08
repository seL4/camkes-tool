#!/usr/bin/env python
# -*- coding: utf-8 -*-

import six

from PyQt5 import QtGui, QtWidgets, QtCore
from camkes.ast import *

# TODO: Make widget totally independent of instance_object, and make controller force AST_creator to search it up everytime,
# TODO: Button for component details
#       Use instance.name as identifier.

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
        self.update_ui()

    @property
    def preferred_point(self):
        raise NotImplementedError

    # Signals & Slots
    openComponentInfo = QtCore.pyqtSignal(Instance)

    def __init__(self, instance_object):
        super(InstanceWidget, self).__init__()
        # Model

        self._instance_object = instance_object
        self._instance_name = instance_object.name

        # GUI
        self.setFrameStyle(QtWidgets.QFrame.Panel)

        layout = QtWidgets.QVBoxLayout()

        self.setLayout(layout)

        self.update_ui()

    def update_ui(self):

        self.clear_canvas()

        layout = self.layout()
        assert isinstance(layout, QtWidgets.QVBoxLayout)

        if self.instance_object:
            string = self.instance_object.name + ": " + self.instance_object.type.name
            new_label = QtWidgets.QLabel(string)

            layout.addWidget(new_label)

            if self.instance_object.type.control:
                layout.addWidget(QtWidgets.QLabel("control;"))

            if self.instance_object.type.hardware:
                layout.addWidget(QtWidgets.QLabel("hardware;"))

    def mousePressEvent(self, mouse_event):
        # Change to must press a button to open component info
        self.openComponentInfo.emit(self.instance_object)

    def mouseMoveEvent(self, QMouseEvent):
        raise NotImplementedError

    def clear_canvas(self):
        layout = self.layout()
        assert isinstance(layout, QtWidgets.QVBoxLayout)

        next_widget = layout.takeAt(0)
        while next_widget is not None:
            del next_widget
            next_widget = layout.takeAt(0)