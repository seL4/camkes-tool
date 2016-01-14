#!/usr/bin/env python
# -*- coding: utf-8 -*-

import six

from PyQt5 import QtGui, QtWidgets, QtCore

# TODO: Make widget totally independent of instance_object, and make controller force AST_creator to search it up everytime,
# TODO: Button for component details
#       Use instance.name as identifier.

import Connection_Widget
from Model import Common

class InstanceWidget(QtWidgets.QGraphicsWidget):

    @property
    def velocity(self):
        if self._velocity is None:
            self._velocity = QtCore.QPointF(0,0)
        return self._velocity

    @velocity.setter
    def velocity(self, value):
        assert isinstance(value, QtCore.QPointF)
        self._velocity = value

    # @property
    # def preferred_point(self):
    #     return self._preferred_point
    #
    # @preferred_point.setter
    # def preferred_point(self, value):
    #     assert isinstance(value, QtCore.QPointF)
    #     self._preferred_point = value

    @property
    def pinned(self):
        return self._pinned

    @pinned.setter
    def pinned(self, value):
        assert isinstance(value, bool)
        self._pinned = value
        
    # --- Information about Instance ---

    @property
    def name(self):
        if self._name is None:
            self._name = "Uninitialised widget"  # TODO make subclass of exception, catch and show a dialog
        return self._name

    @name.setter
    def name(self, value):
        assert isinstance(value, six.string_types)
        self._name = value
        self.update_ui()

    @property
    def component_type(self):
        if self._component_type is None:
            self._component_type = "Uninitialised widget"
        return self._component_type

    @component_type.setter
    def component_type(self, value):
        assert isinstance(value, six.string_types)
        self._component_type = value
        self.update_ui()

    @property
    def control(self):
        return self._control

    @control.setter
    def control(self, value):
        assert isinstance(value, bool)
        self._control = value
        self.update_ui()
        
    @property
    def hardware(self):
        return self._hardware
    
    @hardware.setter
    def hardware(self, value):
        assert isinstance(value, bool)
        self._hardware = value
        self.update_ui()
        
    @property
    def provides(self):
        if self._provides is None:
            self._provides = []
        return self._provides

    def add_provide(self, name, interface_type, connection=None):
        assert isinstance(name, six.string_types)
        assert isinstance(interface_type, six.string_types)

        self.provides.append({'Name': name, 'Interface_type': interface_type, 'Connection_Widget': connection})

        self.update_ui()
        # TODO NotImplementedError

    def add_provide_connection(self, interface_name, connection):
        assert self._provides is not None
        for dictionary in self.provides:
            if dictionary['Name'] == interface_name:
                dictionary['Connection_Widget'] = connection
                break

    def delete_provide(self, name):
        raise NotImplementedError

    @property
    def uses(self):
        if self._uses is None:
            self._uses = []
        return self._uses

    def add_use(self, name, interface_type, connection=None):
        assert isinstance(name, six.string_types)
        assert isinstance(interface_type, six.string_types)

        self.uses.append({'Name': name, 'Interface_type': interface_type, 'Connection_Widget': connection})

        self.update_ui()
        # TODO NotImplementedError

    def add_use_connection(self, interface_name, connection):
        assert self._uses is not None
        for dictionary in self.uses:
            if dictionary['Name'] == interface_name:
                dictionary['Connection_Widget'] = connection
                break

    def delete_use(self, name):
        raise NotImplementedError

    @property
    def emits(self):
        if self._emits is None:
            self._emits = []
        return self._emits

    def add_emit(self, name, interface_type, connection=None):
        assert isinstance(name, six.string_types)
        assert isinstance(interface_type, six.string_types)

        self.emits.append({'Name': name, 'Interface_type': interface_type, 'Connection_Widget': connection})

        self.update_ui()
        # TODO NotImplementedError

    def add_emit_connection(self, interface_name, connection):
        assert self._emits is not None
        for dictionary in self.emits:
            if dictionary['Name'] == interface_name:
                dictionary['Connection_Widget'] = connection
                break

    def delete_emit(self, name):
        raise NotImplementedError

    @property
    def consumes(self):
        if self._consumes is None:
            self._consumes = []
        return self._consumes

    def add_consume(self, name, interface_type, optional, connection=None):
        assert isinstance(name, six.string_types)
        assert isinstance(interface_type, six.string_types)
        assert isinstance(optional, bool)

        self.consumes.append({'Name': name, 'Interface_type': interface_type, 'Optional': optional,
                               'Connection_Widget': connection})

        self.update_ui()
        # TODO NotImplementedError

    def add_consume_connection(self, interface_name, connection):
        assert self._consumes is not None
        for dictionary in self.consumes:
            if dictionary['Name'] == interface_name:
                dictionary['Connection_Widget'] = connection
                break

    def delete_consume(self, name):
        raise NotImplementedError

    @property
    def dataport(self):
        return self._dataport

    def add_dataport(self, name, interface_type, optional, connection=None):
        assert isinstance(name, six.string_types)
        assert isinstance(interface_type, six.string_types)
        assert isinstance(optional, bool)

        if self._dataport is None:
            self._dataport = []

        self._dataport.append({'Name': name, 'Interface_type': interface_type, 'Optional': optional,
                               'Connection_Widget': connection})

        self.update_ui()
        # TODO NotImplementedError

    def add_dataport_connection(self, interface_name, connection):
        assert self._dataport is not None
        for dictionary in self.dataport:
            if dictionary['Name'] == interface_name:
                dictionary['Connection_Widget'] = connection
                break

    def delete_dataport(self, name):
        raise NotImplementedError

    def add_connection(self, connection):

        assert isinstance(connection, Connection_Widget.ConnectionWidget)

        if connection.source_instance_widget is self:
            if connection.source_connection_type == Common.Event:
                self.add_emit_connection(connection.source_interface_name, connection)
            elif connection.source_connection_type == Common.Procedure:
                self.add_use_connection(connection.source_interface_name, connection)
            elif connection.source_connection_type == Common.Dataport:
                self.add_dataport_connection(connection.source_interface_name, connection)

        elif connection.dest_instance_widget is self:
            if connection.dest_connection_type == Common.Event:
                self.add_consume_connection(connection.dest_interface_name, connection)
            elif connection.dest_connection_type == Common.Procedure:
                self.add_provide_connection(connection.dest_interface_name, connection)
            elif connection.dest_connection_type == Common.Dataport:
                self.add_dataport_connection(connection.dest_interface_name, connection)

        else:
            raise NotImplementedError # Something is wrong

    def remove_connection(self, connection):
        raise NotImplementedError

    # -------

    # Signals & Slots
    open_component_info = QtCore.pyqtSignal(six.string_types)
    widget_moved = QtCore.pyqtSignal()

    # TODO: Phase out instance_object
    def __init__(self, preferred_point=None):
        super(InstanceWidget, self).__init__()
        # Model

        self._preferred_point = preferred_point
        self._pinned = False
        self._velocity = None

        self._name = None
        self._component_type = None
        self._control = False
        self._hardware = False
        self._provides = None
        self._uses = None
        self._emits = None
        self._consumes = None
        self._dataport = None

        # GUI
        self.setFlag(QtWidgets.QGraphicsWidget.ItemIsMovable)

        layout = QtWidgets.QGraphicsLinearLayout()
        layout.setOrientation(QtCore.Qt.Vertical)

        self.setLayout(layout)

        self.update_ui()

    def update_ui(self):

        self.clear_canvas()

        layout = self.layout()
        assert isinstance(layout, QtWidgets.QGraphicsLinearLayout)

        string = self.name + ": " + self.component_type
        new_label = QtWidgets.QLabel(string)

        proxy_widget = QtWidgets.QGraphicsProxyWidget()
        proxy_widget.setWidget(new_label)

        layout.addItem(proxy_widget)

        if self.control:
            proxy_widget = QtWidgets.QGraphicsProxyWidget()
            proxy_widget.setWidget(QtWidgets.QLabel("control;"))
            layout.addItem(proxy_widget)

        if self.hardware:
            proxy_widget = QtWidgets.QGraphicsProxyWidget()
            proxy_widget.setWidget(QtWidgets.QLabel("hardware;"))
            layout.addItem(proxy_widget)

    def mousePressEvent(self, mouse_event):
        # Change to must press a button to open component info
        self.open_component_info.emit(self.component_type)

    _moved_at_least_once = False

    def mouseMoveEvent(self, mouse_event):
        self._moved_at_least_once = True
        super(InstanceWidget, self).mouseMoveEvent(mouse_event)

    def itemChange(self, change, value):

        if change == QtWidgets.QGraphicsWidget.ItemPositionHasChanged and self._moved_at_least_once:
            self.pinned = True
            # Tell graph controller that item has moved (signal)

        return super(InstanceWidget, self).itemChange(change, value)



    # previous_position = None
    #
    # def mouseMoveEvent(self, mouse_event):
    #     assert isinstance(mouse_event, QtGui.QMouseEvent)
    #
    #     # print "position is " + str(mouse_event.localPos())
    #
    #     # print "instance widget ------------------------------------------- " + str(self.preferred_point)
    #
    #     if self.previous_position:
    #         assert isinstance(self.previous_position, QtCore.QPointF)
    #         # Calculate relative movement between the movement from the last millisecond (saved below) and
    #         # current position
    #         print "old point is: " + str(self.preferred_point)
    #         print "delta x" + str(mouse_event.x() - self.previous_position.x())
    #         print "delta y" + str(mouse_event.y() - self.previous_position.y())
    #         self.preferred_point = QtCore.QPointF(self.preferred_point.x() + (mouse_event.x() - self.previous_position.x()),
    #                                               self.preferred_point.y() + (mouse_event.y() - self.previous_position.y()))
    #         print "new Point is: " + str(self.preferred_point)
    #         self.widget_moved.emit()
    #         self.previous_position = None
    #     else:
    #         self.previous_position = mouse_event.localPos()
    #
    # def mouseReleaseEvent(self, QMouseEvent):
    #     # Reset delta move position
    #     pass

    def clear_canvas(self):
        layout = self.layout()
        assert isinstance(layout, QtWidgets.QGraphicsLayout)


        while layout.count() > 0:
            next_widget = layout.itemAt(0)
            layout.removeAt(0)
            del next_widget
