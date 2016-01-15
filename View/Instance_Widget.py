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

    _bounding_rect = None

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
                print "found"
                break

    def remove_provide_connection(self, interface_name, connection):
        assert self._provides is not None
        for dictionary in self.provides:
            if dictionary['Name'] == interface_name and dictionary['Connection_Widget'] is connection:
                dictionary['Connection_Widget'] = None
                print "remove"
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
                print "found"
                break

    def remove_use_connection(self, interface_name, connection):
        assert self._uses is not None
        for dictionary in self.uses:
            if dictionary['Name'] == interface_name and dictionary['Connection_Widget'] is connection:
                dictionary['Connection_Widget'] = None
                print "remove"
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
                print "found"
                break

    def remove_emit_connection(self, interface_name, connection):
        assert self._emits is not None
        for dictionary in self.emits:
            if dictionary['Name'] == interface_name and dictionary['Connection_Widget'] is connection:
                dictionary['Connection_Widget'] = None
                print "remove"
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
                print "found"
                break

    def remove_consume_connection(self, interface_name, connection):
        assert self._consumes is not None
        for dictionary in self.consumes:
            if dictionary['Name'] == interface_name and dictionary['Connection_Widget'] is connection:
                dictionary['Connection_Widget'] = None
                print "remove"
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
                print "found"
                break

    def remove_dataport_connection(self, interface_name, connection):
        assert self._dataport is not None
        for dictionary in self.dataport:
            if dictionary['Name'] == interface_name and \
                            dictionary['Connection_Widget'] is connection:
                dictionary['Connection_Widget'] = None
                print "remove"
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
        assert isinstance(connection, Connection_Widget.ConnectionWidget)

        if connection.source_instance_widget is self:
            if connection.source_connection_type == Common.Event:
                self.remove_emit_connection(connection.source_interface_name, connection)
            elif connection.source_connection_type == Common.Procedure:
                self.remove_use_connection(connection.source_interface_name, connection)
            elif connection.source_connection_type == Common.Dataport:
                self.remove_dataport_connection(connection.source_interface_name, connection)

        elif connection.dest_instance_widget is self:
            if connection.dest_connection_type == Common.Event:
                self.remove_consume_connection(connection.dest_interface_name, connection)
            elif connection.dest_connection_type == Common.Procedure:
                self.remove_provide_connection(connection.dest_interface_name, connection)
            elif connection.dest_connection_type == Common.Dataport:
                self.remove_dataport_connection(connection.dest_interface_name, connection)

        else:
            raise NotImplementedError # Something is wrong

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

    _border_thickness = 7

    def update_ui(self):

        self.clear_canvas()

        practise_font = QtGui.QFont("Helvetica", 15, QtGui.QFont.Normal)
        practise_font_metrics = QtGui.QFontMetrics(practise_font)
        instance_name_rect = practise_font_metrics.boundingRect(self.name)

        practise_font.setPointSize(11)
        practise_font_metrics = QtGui.QFontMetrics(practise_font)
        component_name_rect = practise_font_metrics.boundingRect(self.component_type)

        practise_font.setPointSize(12)
        practise_font_metrics = QtGui.QFontMetrics(practise_font)
        control_rect = practise_font_metrics.boundingRect("C")
        hardware_rect = practise_font_metrics.boundingRect("H")

        max_height = 2*self._border_thickness + instance_name_rect.height() + hardware_rect.height() + 2.5

        max_width = 2*self._border_thickness + 2*control_rect.width() + 10
        if instance_name_rect.width() > component_name_rect.width():
            max_width = max_width + instance_name_rect.width()
        else:
            max_width = max_width + component_name_rect.width()

        self._bounding_rect = QtCore.QRectF(0, 0, max_width, max_height)

        self.setPreferredSize(self._bounding_rect.width(), self._bounding_rect.height())

        self.update()

        # layout = self.layout()
        # assert isinstance(layout, QtWidgets.QGraphicsLinearLayout)
        #
        # string = self.name + ": " + self.component_type
        # new_label = QtWidgets.QLabel(string)
        #
        # proxy_widget = QtWidgets.QGraphicsProxyWidget()
        # proxy_widget.setWidget(new_label)
        #
        # layout.addItem(proxy_widget)
        #
        # if self.control:
        #     proxy_widget = QtWidgets.QGraphicsProxyWidget()
        #     proxy_widget.setWidget(QtWidgets.QLabel("control;"))
        #     layout.addItem(proxy_widget)
        #
        # if self.hardware:
        #     proxy_widget = QtWidgets.QGraphicsProxyWidget()
        #     proxy_widget.setWidget(QtWidgets.QLabel("hardware;"))
        #     layout.addItem(proxy_widget)

    def boundingRect(self):
        if self._bounding_rect:
            return self._bounding_rect
        else:
            return super(InstanceWidget, self).boundingRect()

    def paint(self, painter, style_options, widget=None):

        assert isinstance(painter,QtGui.QPainter)
        assert isinstance(style_options,QtWidgets.QStyleOptionGraphicsItem)
        assert isinstance(widget,QtWidgets.QWidget)

        super(InstanceWidget, self).paint(painter,style_options,widget)

        painter.drawRect(self.boundingRect())

        # TODO: Update rect with new size

        # Printing instance name
        font = QtGui.QFont("Helvetica", 15, QtGui.QFont.Normal)
        painter.setFont(font)
        font_metrics = painter.fontMetrics()
        assert isinstance(font_metrics, QtGui.QFontMetrics)
        bounding_rect_font = painter.boundingRect(QtCore.QRectF(1,1,1,1), QtCore.Qt.AlignCenter, self.name)

        bounding_rect_font.moveTo(self.boundingRect().center().x() - bounding_rect_font.width()/2,
                                  self.boundingRect().center().y() - font_metrics.ascent())

        painter.drawText(bounding_rect_font,QtCore.Qt.AlignCenter, self.name)

        control_hardware_x_pos = bounding_rect_font.x()

        # Printing component name
        font.setPointSize(11)
        painter.setFont(font)
        bounding_rect_font = painter.boundingRect(QtCore.QRectF(1,1,1,1), QtCore.Qt.AlignCenter, self.component_type)

        bounding_rect_font.moveTo(self.boundingRect().center().x() - bounding_rect_font.width()/2,
                                  self.boundingRect().center().y())

        painter.drawText(bounding_rect_font,QtCore.Qt.AlignCenter, self.component_type)

        if bounding_rect_font.x() < control_hardware_x_pos:
            control_hardware_x_pos = bounding_rect_font.x()

        control_hardware_x_pos -= 5

        # The C

        font.setPointSize(12)
        painter.setFont(font)
        font_metrics = painter.fontMetrics()
        bounding_rect_font = painter.boundingRect(QtCore.QRectF(1,1,1,1), QtCore.Qt.AlignCenter, "C")

        bounding_rect_font.moveTo(control_hardware_x_pos - bounding_rect_font.width(),
                                  self.boundingRect().center().y() - font_metrics.ascent())
        if self.control:
            painter.drawText(bounding_rect_font,QtCore.Qt.AlignCenter, "C")

        # The H
        bounding_rect_font = painter.boundingRect(QtCore.QRectF(1,1,1,1), QtCore.Qt.AlignCenter, "H")
        bounding_rect_font.moveTo(control_hardware_x_pos - bounding_rect_font.width(),
                                  self.boundingRect().center().y())
        if self.hardware:
            painter.drawText(bounding_rect_font,QtCore.Qt.AlignCenter, "H")



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
