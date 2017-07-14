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

from Interface.Property import PropertyInterface
import Connection_Widget
from Instance_Widget import InstanceWidget

class ConnectionPropertyWidget(QtWidgets.QGroupBox):
    """
    ConnectionPropertyWidget - shows the properties of a connection.
    """

    # Connection Widget that this widget represent
    @property
    def connection_widget(self):
        assert self._connection_widget is not None
        return self._connection_widget

    @connection_widget.setter
    def connection_widget(self, value):
        assert isinstance(value, Connection_Widget.ConnectionWidget)
        self._connection_widget = value

    # views

    @property
    def name_widget(self):
        if self._name_widget is None:
            self._name_widget = QtWidgets.QLabel(self.connection_widget.name)
        return self._name_widget

    @property
    def type_widget(self):
        # When this becomes editable
        # This will be not a label, but a drop down menu
        if self._type_widget is None:
            self._type_widget = QtWidgets.QLabel(self.connection_widget.connection_type)
        return self._type_widget

    @property
    def from_interface_widget(self):
        # When this becomes editable
        # This will be not a label, but a drop down menu
        if self._from_interface_widget is None:
            self._from_interface_widget = QtWidgets.QLabel("%s : %s" % (self.connection_widget.source_interface_name, self.connection_widget.source_connection_type) )
        return self._from_interface_widget

    @property
    def from_instance_widget(self):
        if self._from_instance_widget is None:
            self._from_instance_widget = QtWidgets.QLabel(self.connection_widget.source_instance_widget.name)
        return self._from_instance_widget

    @property
    def to_interface_widget(self):
        # When this becomes editable
        # This will be not a label, but a drop down menu
        if self._to_interface_widget is None:
            self._to_interface_widget = QtWidgets.QLabel("%s : %s" % (self.connection_widget.dest_interface_name, self.connection_widget.dest_connection_type) )
        return self._to_interface_widget

    @property
    def to_instance_widget(self):
        if self._to_instance_widget is None:
            self._to_instance_widget = QtWidgets.QLabel(self.connection_widget.dest_instance_widget.name)
        return self._to_instance_widget

    # --- INITIALISATION ---

    def __init__(self, connection_widget):
        self._connection_widget = None
        self._name_widget = None
        self._type_widget = None
        self._from_interface_widget = None
        self._from_instance_widget = None
        self._to_interface_widget = None
        self._to_instance_widget = None

        self.connection_widget = connection_widget

        super(ConnectionPropertyWidget, self).__init__()

        grid_layout = QtWidgets.QGridLayout()

        # Following must be done after setting connection widget
        # Name
        grid_layout.addWidget(QtWidgets.QLabel("Name: "), 0, 0)
        grid_layout.addWidget(self.name_widget, 0, 1)

        # Type
        grid_layout.addWidget(QtWidgets.QLabel("Type: "), 1, 0)
        grid_layout.addWidget(self.type_widget, 1, 1)

        # Separator
        separator = QtWidgets.QFrame()
        separator.setFrameStyle(QtWidgets.QFrame.HLine | QtWidgets.QFrame.Plain)
        grid_layout.addWidget(separator, 2, 0, 1, -1)

        # Source Instance
        grid_layout.addWidget(QtWidgets.QLabel("Source"), 3, 0, 1, -1)

        grid_layout.addWidget(QtWidgets.QLabel("Interface: "), 4, 0)
        grid_layout.addWidget(self.from_interface_widget, 4, 1)

        grid_layout.addWidget(QtWidgets.QLabel("Instance: "), 5, 0)
        grid_layout.addWidget(self.from_instance_widget, 5, 1)

        # Separator
        separator = QtWidgets.QFrame()
        separator.setFrameStyle(QtWidgets.QFrame.HLine | QtWidgets.QFrame.Plain)
        grid_layout.addWidget(separator, 6, 0, 1, -1)

        # Destination Instance
        grid_layout.addWidget(QtWidgets.QLabel("Destination"), 7, 0, 1, -1)

        grid_layout.addWidget(QtWidgets.QLabel("Interface: "), 8, 0)
        grid_layout.addWidget(self.to_interface_widget, 8, 1)

        grid_layout.addWidget(QtWidgets.QLabel("Instance: "), 9, 0)
        grid_layout.addWidget(self.to_instance_widget, 9, 1)

        self.setLayout(grid_layout)
