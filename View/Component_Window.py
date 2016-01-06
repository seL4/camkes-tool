#!/usr/bin/env python
# -*- coding: utf-8 -*-

import six

from PyQt5 import QtGui, QtWidgets, QtCore
from camkes.ast import *


class ComponentWindow(QtWidgets.QGroupBox):

    @property
    def component_object(self):
        return self._component_object

    def set_component_object(self, value, mouse_event):
        assert isinstance(value, Component)
        self._component_object = value

        assert isinstance(mouse_event, QtGui.QMouseEvent)
        self.move(mouse_event.globalPos())

        self.update_ui()

    def __init__(self, component_obj):
        super(ComponentWindow, self).__init__()
        self.setWindowFlags(QtCore.Qt.Window)

        assert isinstance(component_obj, Component) or component_obj is None
        self._component_object = component_obj

        layout = QtWidgets.QVBoxLayout()
        self.setLayout(layout)

        self.update_ui()

    def update_ui(self):
        if self.component_object is None:
            self.setTitle("No instance selected")
        else:
            self.setTitle(str(self.component_object.name))

            if self.component_object.control:
                self.layout().addWidget(QtWidgets.QLabel("control;"))

            if self.component_object.hardware:
                self.layout().addWidget(QtWidgets.QLabel("hardware;"))
            # TODO: more stuff

        self.show()
