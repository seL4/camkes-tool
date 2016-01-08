#!/usr/bin/env python
# -*- coding: utf-8 -*-

import six

from PyQt5 import QtGui, QtWidgets, QtCore
from camkes.ast import *


class ComponentWindow(QtWidgets.QGroupBox):

    @property
    def component_object(self):
        return self._component_object

    @component_object.setter
    def component_object(self, value):
        assert isinstance(value, Component)
        self._component_object = value

        self.update_ui()

    def __init__(self, component_obj):
        super(ComponentWindow, self).__init__()
        self.setWindowFlags(QtCore.Qt.Window)

        assert isinstance(component_obj, Component) or component_obj is None
        self._component_object = component_obj

        layout = QtWidgets.QVBoxLayout()
        self.setLayout(layout)

        self.control_checkbox = QtWidgets.QCheckBox("Control")
        self.control_checkbox.setChecked(False)
        self.control_checkbox.setDisabled(True)

        self.hardware_checkbox = QtWidgets.QCheckBox("Hardware")
        self.hardware_checkbox.setChecked(False)
        self.hardware_checkbox.setDisabled(True)

        self.provides_label = QtWidgets.QLabel("Provides")

        layout.addWidget(self.control_checkbox)
        layout.addWidget(self.hardware_checkbox)
        layout.addWidget(self.provides_label)



        self.update_ui()

    def update_ui(self):

        layout = self.layout()
        assert isinstance(layout, QtWidgets.QLayout)

        self.show()

        if self.component_object is None:
            self.setTitle("No instance selected")
        else:
            self.setTitle(str(self.component_object.name))

            if self.component_object.control:
                self.control_checkbox.setChecked(True)
            else:
                self.control_checkbox.setChecked(False)

            if self.component_object.hardware:
                self.hardware_checkbox.setChecked(True)
            else:
                self.hardware_checkbox.setChecked(False)

            if len(self.component_object.provides) > 0:
                print "true"
                self.provides_label.show()

                # Need to put a textedit to show provides contents

            else:
                print "false"
                self.provides_label.hide()
                # need to delete textedit from above



            # TODO: more stuff


