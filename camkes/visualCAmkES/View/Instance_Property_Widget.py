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

from PyQt5 import QtWidgets

import Instance_Widget
from Interface.Property import PropertyInterface
import Connection_Widget

class InstancePropertyWidget(QtWidgets.QGroupBox):
    """
    ConnectionPropertyWidget - shows the properties of a connection.
    """

    # Connection Widget that this widget represent
    @property
    def instance_widget(self):
        assert self._instance_widget is not None
        return self._instance_widget

    @instance_widget.setter
    def instance_widget(self, value):
        assert isinstance(value, Instance_Widget.InstanceWidget)
        self._instance_widget = value

    # views

    @property
    def name_widget(self):
        if self._name_widget is None:
            self._name_widget = QtWidgets.QLabel(self.instance_widget.name)
        return self._name_widget

    @property
    def type_widget(self):
        # When this becomes editable
        # This will be not a label, but a drop down menu
        if self._type_widget is None:
            self._type_widget = QtWidgets.QLabel(self.instance_widget.component_type)
        return self._type_widget

    @property
    def hardware_widget(self):
        if self._hardware_widget is None and self.instance_widget.hardware:
            self._hardware_widget = QtWidgets.QLabel("Hardware")
        return self._hardware_widget

    @property
    def control_widget(self):
        if self._control_widget is None and self.instance_widget.control:
            self._control_widget = QtWidgets.QLabel("Control")
        return self._control_widget

    # --- INITIALISATION ---

    def __init__(self, instance_widget):
        self._instance_widget = None
        self._name_widget = None
        self._type_widget = None
        self._hardware_widget = None
        self._control_widget = None

        self.instance_widget = instance_widget

        super(InstancePropertyWidget, self).__init__()

        grid_layout = QtWidgets.QGridLayout()

        row = 0
        # Following must be done after setting instance widget
        # Name
        grid_layout.addWidget(QtWidgets.QLabel("Name: "), row, 0)
        grid_layout.addWidget(self.name_widget, row, 1)
        row = row + 1

        # Type
        grid_layout.addWidget(QtWidgets.QLabel("Type: "), row, 0)
        grid_layout.addWidget(self.type_widget, row, 1)
        row = row + 1

        # Hardware
        if self.hardware_widget:
            grid_layout.addWidget(self.hardware_widget, row, 0, 1, -1)
            row = row + 1

        # Control
        if self.control_widget:
            grid_layout.addWidget(self.control_widget, row, 0, 1, -1)
            row = row + 1

        # Separator
        separator = QtWidgets.QFrame()
        separator.setFrameStyle(QtWidgets.QFrame.HLine | QtWidgets.QFrame.Plain)
        grid_layout.addWidget(separator, row, 0, 1, -1)
        row = row + 1

        # List all connection
        grid_layout.addWidget(QtWidgets.QLabel("Connections"), row, 0, 1, -1)
        row = row + 1

        for provide_dict in self.instance_widget.provides:
            grid_layout.addWidget(QtWidgets.QLabel("Procedure"), row, 0)
            grid_layout.addWidget(QtWidgets.QLabel("%s : %s" % (provide_dict["Interface_type"], provide_dict["Name"]) ), row, 1)
            row = row + 1

        for use_dict in self.instance_widget.uses:
            grid_layout.addWidget(QtWidgets.QLabel("Procedure"), row, 0)
            grid_layout.addWidget(QtWidgets.QLabel("%s : %s" % (use_dict["Interface_type"], use_dict["Name"]) ), row, 1)
            row = row + 1

        for emit_dict in self.instance_widget.emits:
            grid_layout.addWidget(QtWidgets.QLabel("Event"), row, 0)
            grid_layout.addWidget(QtWidgets.QLabel("%s : %s" % (emit_dict["Interface_type"], emit_dict["Name"]) ), row, 1)
            row = row + 1

        for consume_dict in self.instance_widget.consumes:
            grid_layout.addWidget(QtWidgets.QLabel("Event"), row, 0)
            grid_layout.addWidget(QtWidgets.QLabel("%s : %s" % (consume_dict["Interface_type"], consume_dict["Name"]) ), row, 1)
            row = row + 1

        for dataport_dict in self.instance_widget.dataport:
            grid_layout.addWidget(QtWidgets.QLabel("Dataport"), row, 0)
            grid_layout.addWidget(QtWidgets.QLabel("%s : %s" % (dataport_dict["Interface_type"], dataport_dict["Name"]) ), row, 1)
            row = row + 1

        self.setLayout(grid_layout)
