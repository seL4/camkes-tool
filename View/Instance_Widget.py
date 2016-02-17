#!/usr/bin/env python
# -*- coding: utf-8 -*-

import six, math, random

random.seed(20)

from PyQt5 import QtGui, QtWidgets, QtCore

import Connection_Widget
from Model import Common

# TODO: Delete itself from all connections when __del__ ed

class InstanceWidget(QtWidgets.QGraphicsWidget):

    # Constants and private class variables
    _bounding_rect = None
    _border_thickness = 7

    @property
    def velocity(self):
        if self._velocity is None:
            self._velocity = QtCore.QPointF(0, 0)
        return self._velocity

    @velocity.setter
    def velocity(self, value):
        assert isinstance(value, QtCore.QPointF)
        self._velocity = value

    # --- Information about Instance ---

    @property
    def name(self):
        if self._name is None:
            self._name = "Uninitialised widget"
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

    # Provides
    @property
    def provides(self):
        if self._provides is None:
            self._provides = []
        return self._provides

    # TODO: Handle multiple connections
    def add_provide(self, name, interface_type, connection=None):
        assert isinstance(name, six.string_types)
        assert isinstance(interface_type, six.string_types)

        self.provides.append({'Name': name, 'Interface_type': interface_type, 'Connection_Widget': connection})

        self.update_ui()

    def add_provide_connection(self, interface_name, connection):
        assert self._provides is not None
        for dictionary in self.provides:
            if dictionary['Name'] == interface_name:
                dictionary['Connection_Widget'] = connection
                break

    def remove_provide_connection(self, interface_name, connection):
        assert self._provides is not None
        for dictionary in self.provides:
            if dictionary['Name'] == interface_name and dictionary['Connection_Widget'] is connection:
                dictionary['Connection_Widget'] = None
                break

    def delete_provide(self, name):
        raise NotImplementedError

    # Uses
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

    def remove_use_connection(self, interface_name, connection):
        assert self._uses is not None
        for dictionary in self.uses:
            if dictionary['Name'] == interface_name and dictionary['Connection_Widget'] is connection:
                dictionary['Connection_Widget'] = None
                break

    def delete_use(self, name):
        raise NotImplementedError

    # Emits
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

    def remove_emit_connection(self, interface_name, connection):
        assert self._emits is not None
        for dictionary in self.emits:
            if dictionary['Name'] == interface_name and dictionary['Connection_Widget'] is connection:
                dictionary['Connection_Widget'] = None
                break

    def delete_emit(self, name):
        raise NotImplementedError

    # Consumes
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

    def remove_consume_connection(self, interface_name, connection):
        assert self._consumes is not None
        for dictionary in self.consumes:
            if dictionary['Name'] == interface_name and dictionary['Connection_Widget'] is connection:
                dictionary['Connection_Widget'] = None
                break

    def delete_consume(self, name):
        raise NotImplementedError

    # Dataport
    @property
    def dataport(self):
        if self._dataport is None:
            self._dataport = []
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

    def remove_dataport_connection(self, interface_name, connection):
        assert self._dataport is not None
        for dictionary in self.dataport:
            if dictionary['Name'] == interface_name and \
                            dictionary['Connection_Widget'] is connection:
                dictionary['Connection_Widget'] = None
                break

    def delete_dataport(self, name):
        raise NotImplementedError

    @property
    def connection_list(self):
        return self._connections_list

    # TODO: connection overrides, for multiway connection. Eg. eigenConnection
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
            raise NotImplementedError  # Something is wrong

        self._connections_list.append(connection)
        self.update_connection_position(connection)

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
            raise NotImplementedError  # Something is wrong

        self._connections_list.remove(connection)

    # -------

    # Signals & Slots
    open_component_info = QtCore.pyqtSignal(six.string_types)
    widget_moved = QtCore.pyqtSignal()

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

        self._connections_list = []

        # GUI
        self.color = QtGui.QColor(245,245,245)

        self.setFlag(QtWidgets.QGraphicsWidget.ItemIsMovable)

        layout = QtWidgets.QGraphicsLinearLayout()
        layout.setOrientation(QtCore.Qt.Vertical)

        self.setLayout(layout)

        self.update_ui()

    # --- UI Functions ---

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

        max_height = 2 * self._border_thickness + instance_name_rect.height() + hardware_rect.height() + 7

        max_width = 2 * self._border_thickness + 2 * control_rect.width() + 10
        if instance_name_rect.width() > component_name_rect.width():
            max_width = max_width + instance_name_rect.width()
        else:
            max_width = max_width + component_name_rect.width()

        self._bounding_rect = QtCore.QRectF(0, 0, max_width, max_height)

        self.setPreferredSize(self._bounding_rect.width(), self._bounding_rect.height())

        self.update()

    def boundingRect(self):
        return self._bounding_rect

    def paint(self, painter, style_options, widget=None):

        assert isinstance(painter, QtGui.QPainter)
        assert isinstance(style_options, QtWidgets.QStyleOptionGraphicsItem)
        # assert isinstance(widget, QtWidgets.QWidget)

        super(InstanceWidget, self).paint(painter, style_options, widget)

        painter.setRenderHint(QtGui.QPainter.Antialiasing)

        rounded_rect = QtGui.QPainterPath()
        assert isinstance(rounded_rect, QtGui.QPainterPath)
        rounded_rect.addRoundedRect(self.boundingRect(),5,5)

        # painter.fillRect(self.boundingRect(), self.color)
        # painter.drawRect(self.boundingRect())
        painter.fillPath(rounded_rect, self.color)
        painter.drawPath(rounded_rect)

        # TODO: Update rect with new size

        # Printing instance name
        font = QtGui.QFont("Helvetica", 15, QtGui.QFont.Normal)
        painter.setFont(font)
        font_metrics = painter.fontMetrics()
        assert isinstance(font_metrics, QtGui.QFontMetrics)
        bounding_rect_font = painter.boundingRect(QtCore.QRectF(1, 1, 1, 1), QtCore.Qt.AlignCenter, self.name)

        bounding_rect_font.moveTo(self.boundingRect().center().x() - bounding_rect_font.width() / 2,
                                  self.boundingRect().center().y() - font_metrics.ascent())

        painter.drawText(bounding_rect_font, QtCore.Qt.AlignCenter, self.name)

        control_hardware_x_pos = bounding_rect_font.x()

        # Printing component name
        font.setPointSize(11)
        painter.setFont(font)
        bounding_rect_font = painter.boundingRect(QtCore.QRectF(1, 1, 1, 1), QtCore.Qt.AlignCenter, self.component_type)

        bounding_rect_font.moveTo(self.boundingRect().center().x() - bounding_rect_font.width() / 2,
                                  self.boundingRect().center().y() + font_metrics.descent())

        painter.drawText(bounding_rect_font, QtCore.Qt.AlignCenter, self.component_type)

        if bounding_rect_font.x() < control_hardware_x_pos:
            control_hardware_x_pos = bounding_rect_font.x()

        control_hardware_x_pos -= 5

        # The C

        font.setPointSize(12)
        painter.setFont(font)
        font_metrics = painter.fontMetrics()
        bounding_rect_font = painter.boundingRect(QtCore.QRectF(1, 1, 1, 1), QtCore.Qt.AlignCenter, "C")

        bounding_rect_font.moveTo(control_hardware_x_pos - bounding_rect_font.width(),
                                  self.boundingRect().center().y() - font_metrics.ascent())
        if self.control:
            painter.drawText(bounding_rect_font, QtCore.Qt.AlignCenter, "C")

        # The H
        bounding_rect_font = painter.boundingRect(QtCore.QRectF(1, 1, 1, 1), QtCore.Qt.AlignCenter, "H")
        bounding_rect_font.moveTo(control_hardware_x_pos - bounding_rect_font.width(),
                                  self.boundingRect().center().y() + font_metrics.descent())
        if self.hardware:
            painter.drawText(bounding_rect_font, QtCore.Qt.AlignCenter, "H")

    # --- Event Handling ---
    def itemChange(self, change, value):

        if change == QtWidgets.QGraphicsWidget.ItemPositionHasChanged:  # and self._moved_at_least_once:
            self.update_connections()

        return super(InstanceWidget, self).itemChange(change, value)

    def mousePressEvent(self, mouse_event):
        # Change to must press a button to open component info

        string = " "

        for connection in self.connection_list:
            string += connection.name + " "

        print self.name + " contains: " + string

        no_of_connections = len(self.dataport) + len(self.provides) + len(self.consumes) + len(self.uses) + \
                            len(self.emits)
        print "\tNumber of connections is: " + str(no_of_connections)
        print "\tdataport: " + str(len(self.dataport))
        print "\tprovides: " + str(len(self.provides))
        print "\tconsumes: " + str(len(self.consumes))
        print "\tuses: " + str(len(self.uses))
        print "\temits: " + str(len(self.emits))

        self.open_component_info.emit(self.component_type)

    _moved_at_least_once = False

    def mouseMoveEvent(self, mouse_event):
        self._moved_at_least_once = True
        self.widget_moved.emit()
        super(InstanceWidget, self).mouseMoveEvent(mouse_event)

    def update_connections(self):

        for connection in self.connection_list:
            self.update_connection_position(connection)
            if connection.source_instance_widget is self:
                connection.dest_instance_widget.update_connection_position(connection)
            else:
                connection.source_instance_widget.update_connection_position(connection)

    def update_connection_position(self, connection):
        assert isinstance(connection, Connection_Widget.ConnectionWidget)
        # print "This is " + self.name + " and updating: " + str(connection.name)

        angle = 0
        angle_set = False
        decrease_angle = False

        # other_widget = None
        if connection.source_instance_widget is self:
            other_widget = connection.dest_instance_widget
            if connection.dest_angle:
                angle_set = True
                if connection.dest_angle < 0:
                    decrease_angle = True
        else:
            other_widget = connection.source_instance_widget
            if connection.source_angle:
                angle_set = True
            if connection.source_angle < 0:
                decrease_angle = True

        # TODO: Inefficient algorithm

        # --- Find position based on straight line distance between this and other widget ---

        # Vector between other and this
        assert isinstance(other_widget, InstanceWidget)

        our_pos = self.scenePos()
        our_pos.setX(our_pos.x() + self.boundingRect().width() / 2)
        our_pos.setY(our_pos.y() + self.boundingRect().height() / 2)

        other_widget_pos = other_widget.scenePos()
        other_widget_pos.setX(other_widget_pos.x() + self.boundingRect().width() / 2)
        other_widget_pos.setY(other_widget_pos.y() + self.boundingRect().height() / 2)

        vector = other_widget_pos - our_pos

        # print "Connection " + connection.name + " from: " + str(connection.source_instance_widget.name) + " to " + str(
        #         connection.dest_instance_widget.name)
        # print "\tother position:" + str(other_widget_pos) + " ours:" + str(our_pos)
        # print "\tvector: " + str(vector)
        # print "\tbounding rect: " + str(self.boundingRect())

        if vector.x() == 0:
            y = self.boundingRect().height() # To force into "Yo here 3/4"
        else:
            y = vector.y() * math.fabs((self.boundingRect().width() / 2) / vector.x())
        # print "\ty is : " + str(y)

        half_height = self.boundingRect().height() / 2 + 1  # Bit of room for rounding

        if -half_height <= y <= half_height:
            vector.setY(y)
            if vector.x() < 0:
                # print "\tYo here 1"
                vector.setX(-self.boundingRect().width() / 2)
            else:
                # print "\tYo here 2"
                vector.setX(self.boundingRect().width() / 2)
        else:

            if vector.y() == 0:
                x = self.boundingRect().width()
            else:
                x = vector.x() * math.fabs((self.boundingRect().height() / 2) / vector.y())

            vector.setX(x)
            if vector.y() < 0:
                # print "\tYo here 3"
                vector.setY(-self.boundingRect().height() / 2)
            else:
                # print "\tYo here 4"
                vector.setY(self.boundingRect().height() / 2)

        # print "\tnew vector: " + str(vector)

        final_pos = our_pos + vector

        # --- Choose an angle, start with 0 degrees, and search through all connection points, looking for clashes

        for compare in self.connection_list:
            assert isinstance(compare, Connection_Widget.ConnectionWidget)

            # print "\tchecking clash with: " + str(compare.name)

            if compare is connection:
                continue


            if compare.source_instance_widget is self:
                compare_pos = compare.source_pos
                compare_angle = compare.source_angle
            elif compare.dest_instance_widget is self:
                compare_pos = compare.dest_pos
                compare_angle = compare.dest_angle
            else:
                raise NotImplementedError  # Something went wrong

            if compare_pos != final_pos:
                # print "\t\tdoes not clash"
                continue

            # print "\t\ttheir angle is " + str(compare_angle) + " and ours is " + str(angle)

            while compare_angle == angle:
                # print "\t\ttried angle " + str(angle) + ", clashed"

                if angle_set:
                    if decrease_angle:
                        angle += 35
                    else:
                        angle -= 35
                else:
                    angle = -angle
                    if decrease_angle:
                        angle -= 35

                    decrease_angle = not decrease_angle

        if connection.source_instance_widget is self:
            connection.set_source_pos_angle(final_pos, angle)
        else:
            connection.set_dest_pos_angle(final_pos, angle)

    def clear_canvas(self):
        layout = self.layout()
        assert isinstance(layout, QtWidgets.QGraphicsLayout)

        while layout.count() > 0:
            next_widget = layout.itemAt(0)
            layout.removeAt(0)
            del next_widget
