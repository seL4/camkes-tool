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

import six
import math

from PyQt5 import QtGui, QtWidgets, QtCore

import Connection_Widget
from Model import Common
from Interface.Property import PropertyInterface
from Instance_Property_Widget import InstancePropertyWidget

# TODO: Delete itself from all connections when __del__ ed

class InstanceWidget(QtWidgets.QGraphicsWidget, PropertyInterface):
    """
    InstanceWidget - a View representation of camkes.ast.Instance.
    If model changes, update the fields in InstanceWidget.
    """

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

    @property
    def hidden(self):
        return self._hidden

    @hidden.setter
    def hidden(self, value):
        assert isinstance(value, bool)
        self._hidden = value

        if value:
            self.setZValue(3)
        else:
            self.setZValue(5)

        for connection in self.connection_list:
            # This will only set if both source and destination is not hidden
            connection.hidden = value
            connection.update()

        self.update()

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

        self.provides.append({'Name': name,
                              'Interface_type': interface_type,
                              'Connection_Widget': connection})

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
            if dictionary['Name'] == interface_name and \
                    dictionary['Connection_Widget'] is connection:
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

    @property
    def context_menu(self):
        return self._context_menu

    @context_menu.setter
    def context_menu(self, value):
        assert isinstance(value, QtWidgets.QGraphicsProxyWidget)
        assert isinstance(value.widget(), QtWidgets.QMenu)
        self._context_menu = value

    @property
    def property_widget(self):
        self._property_widget = InstancePropertyWidget(self)
        return self._property_widget
    # -------

    # Signals & Slots
    widget_moved = QtCore.pyqtSignal()

    # --- INITIALISATION
    def __init__(self, context_menu, preferred_point=None):
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

        self._context_menu = None
        self.context_menu = context_menu
        self._hidden = False
        self._property_widget = None

        self._connections_list = []

        # GUI
        self.color = QtGui.QColor(245,245,245)

        self.setFlag(QtWidgets.QGraphicsWidget.ItemIsMovable)

        self.update_ui()

    # --- UI FUNCTIONS ---
    def paint(self, painter, style_options, widget=None):
        """
        Overridden function, paints the box with name, type and the C H symbols.
        :param painter:
        :param style_options:
        :param widget:
        :return:
        """

        assert isinstance(painter, QtGui.QPainter)
        assert isinstance(style_options, QtWidgets.QStyleOptionGraphicsItem)
        # assert isinstance(widget, QtWidgets.QWidget)

        super(InstanceWidget, self).paint(painter, style_options, widget)

        painter.setRenderHint(QtGui.QPainter.Antialiasing)

        # -- If hidden, changing alpha values to transparent --
        color = self.color

        if self.hidden:
            color.setAlphaF(0.2)
        else:
            color.setAlphaF(1)

        # Setting brush color
        brush = painter.brush()
        brush.setColor(color)
        painter.setBrush(brush)

        pen = painter.pen()
        pen_color = pen.color()
        if self.hidden:
            pen_color.setAlphaF(0.2)
        else:
            pen_color.setAlphaF(1)
        pen.setColor(pen_color)
        painter.setPen(pen)

        rounded_rect = QtGui.QPainterPath()
        assert isinstance(rounded_rect, QtGui.QPainterPath)
        # If instance is control or hardware, boundedRect will compensate for that.
        inner_rect = self.boundingRect().adjusted(0,0,0,0)  # Hacking way to get a copy of rect
        if self.hardware or self.control:
            inner_rect.adjust(2,2,-2,-2)
        rounded_rect.addRoundedRect(inner_rect,5,5)

        painter.fillPath(rounded_rect, color)
        painter.drawPath(rounded_rect)

        # Draw an outline if the instance is control or hardware
        # Assumption is, an instance cannot be both control and hardware
        outline_rect = inner_rect.adjusted(-1,-1,1,1)
        outline_rect_path = QtGui.QPainterPath()
        outline_rect_path.addRoundedRect(outline_rect, 5, 5)
        stroker = QtGui.QPainterPathStroker()
        stroker.setWidth(5)
        outline_rounded_rect = stroker.createStroke(outline_rect_path)

        # Draw outline to highlight control components
        if self.control:
            # Make a BLUE color pen
            pen_color.setRed(30)
            pen_color.setGreen(136)
            pen_color.setBlue(229)
            painter.fillPath(outline_rounded_rect, pen_color)

        # Draw outline to highlight hardware components
        if self.hardware:
            pen_color.setRed(67)
            pen_color.setGreen(160)
            pen_color.setBlue(71)
            painter.fillPath(outline_rounded_rect, pen_color)

        # TODO IDEA: Update rect with new size

        # Printing instance name
        font = QtGui.QFont("Helvetica", 15, QtGui.QFont.Normal)
        painter.setFont(font)
        font_metrics = painter.fontMetrics()
        assert isinstance(font_metrics, QtGui.QFontMetrics)
        bounding_rect_font = painter.boundingRect(QtCore.QRectF(1, 1, 1, 1), QtCore.Qt.AlignCenter, self.name)

        bounding_rect_font.moveTo(inner_rect.center().x() - bounding_rect_font.width() / 2,
                                  inner_rect.center().y() - font_metrics.ascent())

        painter.drawText(bounding_rect_font, QtCore.Qt.AlignCenter, self.name)

        control_hardware_x_pos = bounding_rect_font.x()

        # Printing component name
        font.setPointSize(11)
        painter.setFont(font)
        bounding_rect_font = painter.boundingRect(QtCore.QRectF(1, 1, 1, 1), QtCore.Qt.AlignCenter, self.component_type)

        bounding_rect_font.moveTo(inner_rect.center().x() - bounding_rect_font.width() / 2,
                                  inner_rect.center().y() + font_metrics.descent())

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
                                  inner_rect.center().y() - font_metrics.ascent())
        if self.control:
            painter.drawText(bounding_rect_font, QtCore.Qt.AlignCenter, "C")

        # The H
        bounding_rect_font = painter.boundingRect(QtCore.QRectF(1, 1, 1, 1), QtCore.Qt.AlignCenter, "H")
        bounding_rect_font.moveTo(control_hardware_x_pos - bounding_rect_font.width(),
                                  inner_rect.center().y() + font_metrics.descent())
        if self.hardware:
            painter.drawText(bounding_rect_font, QtCore.Qt.AlignCenter, "H")

    def update_ui(self):
        """
        Recalculates the expected size of the view, and calls a repaint.
        :return:
        """

        # Calculate rect for instance name
        practise_font = QtGui.QFont("Helvetica", 15, QtGui.QFont.Normal)
        practise_font_metrics = QtGui.QFontMetrics(practise_font)
        instance_name_rect = practise_font_metrics.boundingRect(self.name)

        # Calculate rect for component type
        practise_font.setPointSize(11)
        practise_font_metrics = QtGui.QFontMetrics(practise_font)
        component_name_rect = practise_font_metrics.boundingRect(self.component_type)

        # Calculate rects for control and hardware symbols
        practise_font.setPointSize(12)
        practise_font_metrics = QtGui.QFontMetrics(practise_font)
        control_rect = practise_font_metrics.boundingRect("C")
        hardware_rect = practise_font_metrics.boundingRect("H")

        # Find the max height
        max_height = 2 * self._border_thickness + instance_name_rect.height() + hardware_rect.height() + 7

        # Find the max width
        max_width = 2 * self._border_thickness + 2 * control_rect.width() + 10
        if instance_name_rect.width() > component_name_rect.width():
            max_width = max_width + instance_name_rect.width()
        else:
            max_width = max_width + component_name_rect.width()

        # Set bounding rect to new max width and height
        self._bounding_rect = QtCore.QRectF(self.scenePos().x(), self.scenePos().y(), max_width, max_height)

        # Adjust for new hardware or control border
        if self.hardware or self.control:
            self._bounding_rect.adjust(-2,-2,2,2)

        self.setPreferredSize(self._bounding_rect.width(), self._bounding_rect.height())

        self.update()  # Call a repaint

    def boundingRect(self):
        """
        :return: QRect - bounding rectangle of this widget
        """

        return self._bounding_rect

    def update_connections(self):
        """
        Forces all connections and connecting instances to update.
        :return:
        """

        for connection in self.connection_list:
            self.update_connection_position(connection)
            if connection.source_instance_widget is self:
                connection.dest_instance_widget.update_connection_position(connection)
            else:
                connection.source_instance_widget.update_connection_position(connection)

    def update_connection_position(self, connection):
        """
        Updates the touching point between the connection and this widget.
        :param connection: The connection to be updated
        :return:
        """

        assert isinstance(connection, Connection_Widget.ConnectionWidget)

        decrease_angle = None

        # Find the direction of the angle on the other end - if it is set.
        if connection.source_instance_widget is self:
            other_widget = connection.dest_instance_widget
            if connection.dest_angle:
                decrease_angle = connection.dest_angle >= 0
        else:
            other_widget = connection.source_instance_widget
            if connection.source_angle:
                decrease_angle = connection.source_angle >= 0

        # --- Find position based on straight line distance between this and other widget ---

        # -- Vector between other and this --
        assert isinstance(other_widget, InstanceWidget)

        our_pos = self.scenePos()
        # Get middle of widget
        our_pos.setX(our_pos.x() + self.boundingRect().width() / 2)
        our_pos.setY(our_pos.y() + self.boundingRect().height() / 2)

        other_widget_pos = other_widget.scenePos()
        # Get middle of widget
        other_widget_pos.setX(other_widget_pos.x() + other_widget.boundingRect().width() / 2)
        other_widget_pos.setY(other_widget_pos.y() + other_widget.boundingRect().height() / 2)

        vector = other_widget_pos - our_pos

        # -- Finding intersection between vector and edge of this widget --
        final_pos = self.edge_intersection(our_pos, vector)

        # Check if final_pos is inside other_widget
        # If inside, use the centre of this widget instead.
        other_widget_top_left = other_widget.scenePos()
        other_widget_bottom_right = QtCore.QPointF(other_widget.scenePos().x() + \
                                                           other_widget.boundingRect().width(),
                                                   other_widget.scenePos().y() + \
                                                           other_widget.boundingRect().height())
        if final_pos.x() >= other_widget_top_left.x() and \
            final_pos.x() <= other_widget_bottom_right.x() and \
            final_pos.y() >= other_widget_top_left.y() and \
            final_pos.y() <= other_widget_bottom_right.y():
            final_pos = our_pos

        # Find unclashing angle
        angle = self.find_free_angle(final_pos, connection, decrease_angle)

        # Set our newly found position and angle (at the appropriate side of the connection)
        if connection.source_instance_widget is self:
            connection.set_source_pos_angle(final_pos, angle)
        else:
            connection.set_dest_pos_angle(final_pos, angle)

    # TODO: Potentially inefficient algorithm
    def edge_intersection(self, our_pos, vector):
        """
        Finding the intersection between the vector + pos , to the edge of the widget
        :param our_pos: The starting position of the vector (usually centre of widget)
        :param vector: The vector from the starting position
        :return: PyQt5.QPointF - The position of the intersection with the edge.
        """

        # Consider the case where x is bigger than y
        #            .
        #         .  .
        #     .      .
        # ............
        # We reduce y, proportional to x, such that x is equal to width of widget.

        # If the x is 0, then it is a horizontal
        if vector.x() == 0:
            y_pos = self.boundingRect().height()
            # If original y is negative, new y must also be negative
            if vector.y() < 0:
                y_pos = -y_pos
        else:
            # Using ratios to get y value
            y_pos = vector.y() * math.fabs((self.boundingRect().width() / 2) / vector.x())

        half_height = self.boundingRect().height() / 2 + 1  # Bit of room for rounding

        # If y is within the box then above assumption is correct
        if -half_height <= y_pos <= half_height:
            vector.setY(y_pos)
            if vector.x() < 0:
                vector.setX(-self.boundingRect().width() / 2)
            else:
                vector.setX(self.boundingRect().width() / 2)
        else:
            # If y wasn't within the box, then we assumption is wrong, y is bigger than x
            #      .
            #      .
            #    . .
            #      .
            #   .  .
            #      .
            # ......
            # We reduce x, proportional to y, such that y is equal to height.

            # If y is 0, then it is vertical
            if vector.y() == 0:
                x_pos = self.boundingRect().width()
                if vector.x() < 0:
                    x_pos = -x_pos
            else:
                # Using ratios to get x value
                x_pos = vector.x() * math.fabs((self.boundingRect().height() / 2) / vector.y())

            vector.setX(x_pos)
            if vector.y() < 0:
                vector.setY(-self.boundingRect().height() / 2)
            else:
                vector.setY(self.boundingRect().height() / 2)

        # We got a vector from the center, now we get the final position
        final_pos = our_pos + vector

        return final_pos

    # TODO: Potentially inefficient algorithm
    def find_free_angle(self, pos, connection, decrease_angle=None):
        """
        Find a angle which doesn't collide with any other connection
        at the same position.
        :param pos: Position to find angle
        :param connection: The current connection we are checking for
        :param decrease_angle: If a specific direction is required, then use this variable
                               to specific whether the final angle is positive or negative.
                               Default is None.
        """
        angle = 0

        if decrease_angle is None:
            decrease_angle = False
            angle_set = False
        else:
            angle_set = True

        # Choose an angle, start with 0 degrees, and search through all connection points,
        # looking for clashes
        for compare in self.connection_list:
            assert isinstance(compare, Connection_Widget.ConnectionWidget)

            if compare is connection:
                continue  # Not interested in the same connection, find others

            # Get the current position and angle of the potential clashing connection
            if compare.source_instance_widget is self:
                compare_pos = compare.source_pos
                compare_angle = compare.source_angle
            elif compare.dest_instance_widget is self:
                compare_pos = compare.dest_pos
                compare_angle = compare.dest_angle
            else:
                raise NotImplementedError  # Something went wrong

            if compare_pos != pos:
                continue  # Does not clash, continue searching

            # If clashing, find a angle which doesn't clash
            while compare_angle == angle:
                if angle_set:
                    if decrease_angle:
                        angle -= 35
                    else:
                        angle += 35
                else:
                    # If angle is not set, try 0, -35, 35, -70, 70 etc
                    # In order to alternate between positive and negative,
                    #    use decrease_angle as a toggle
                    angle = -angle
                    if decrease_angle:
                        angle -= 35

                    decrease_angle = not decrease_angle

        return angle

    # --- EVENTS ---
    def itemChange(self, change, value):
        """
        Deals with position changes. Updates connections when ever position changes
        :param change:
        :param value:
        :return:
        """

        if change == QtWidgets.QGraphicsWidget.ItemPositionHasChanged:
            self.update_connections()

        return super(InstanceWidget, self).itemChange(change, value)

    def mousePressEvent(self, mouse_event):
        """
        Deals with instances being pressed. Right now doesn't do anything special other than
        printing the name, type and number of connections
        :param mouse_event:
        :return:
        """

        string = " "

        for connection in self.connection_list:
            string += "%s " % connection.name

        print "%s contains: %s" % (self.name, string)

        no_of_connections = len(self.dataport) + len(self.provides) + len(self.consumes) + len(self.uses) + \
                            len(self.emits)
        print "\tNumber of connections is: %s" % str(no_of_connections)
        print "\tdataport: %s" % str(len(self.dataport))
        print "\tprovides: %s" % str(len(self.provides))
        print "\tconsumes: %s" % str(len(self.consumes))
        print "\tuses: %s" % str(len(self.uses))
        print "\temits: %s" % str(len(self.emits))

    def mouseMoveEvent(self, mouse_event):
        """
        Deals with this instance being clicked and dragged. Emits a signal that component was moved.
        :param mouse_event:
        :return:
        """

        self.widget_moved.emit()
        super(InstanceWidget, self).mouseMoveEvent(mouse_event)

    def contextMenuEvent(self, event):
        """
        Shows a context menu for this instance, asking to either show or hide the component.
        Uses context menu given by graph widget.
        :param event:
        :return:
        """

        assert isinstance(event, QtWidgets.QGraphicsSceneContextMenuEvent)

        # Get menu widget from proxy widget
        menu = self.context_menu.widget()
        assert isinstance(menu, QtWidgets.QMenu)

        # If current hidden, action is "Show" otherwise "Hide"
        menu.clear()
        if self.hidden:
            showComponentAction = menu.addAction("Show component")
            showComponentAction.triggered.connect(self.show_component)
        else:
            hideComponentAction = menu.addAction("Hide component")
            hideComponentAction.triggered.connect(self.hide_component)

        # Set the current position [of proxy widget] to mouse click position
        self.context_menu.setPos(event.scenePos())
        menu.exec_()

    def show_component(self):
        self.hidden = False

    def hide_component(self):
        self.hidden = True
