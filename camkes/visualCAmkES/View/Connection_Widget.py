#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

import math, six

from PyQt5 import QtGui, QtWidgets, QtCore

from Interface.Property import PropertyInterface
from Instance_Widget import InstanceWidget
from Connection_Property_Widget import ConnectionPropertyWidget

class ConnectionWidget(QtWidgets.QGraphicsItem, PropertyInterface):
    """
    ConnectionWidget - a View represetation for the camkes.ast.Connection objects.
    This widget is a one time use. Instead of attempting to sync this connection with the model, just make a new object.
    """

    @property
    def hidden(self):
        return self._hidden

    # Hidden will only work if a source and destination widget exist
    # It will only be set false, if both source and destination is false
    @hidden.setter
    def hidden(self, value):
        assert isinstance(value, bool)
        self._hidden = value or self.source_instance_widget.hidden or \
                       self.dest_instance_widget.hidden
        if self._hidden:
            self.setZValue(2)
        else:
            self.setZValue(4)

    @property
    def name(self):
        return self._connection_name

    @name.setter
    def name(self, value):
        assert isinstance(value, six.string_types)
        self._connection_name = value
        self.setToolTip("%s : %s" % (value, self.connection_type))

    @property
    def connection_type(self):
        return self._connection_type

    @connection_type.setter
    def connection_type(self, value):
        assert isinstance(value, six.string_types)
        self._connection_type = value
        self.setToolTip("%s : %s" % (self.name, value) )

    @property
    def path(self):
        # Lazy Instantiation
        if self._path is None:
            self._path = QtGui.QPainterPath()
        return self._path

    def clear_path(self):
        self._path = None

    # Source information
    @property
    def source_instance_widget(self):
        return self._source_instance_widget

    @source_instance_widget.setter
    def source_instance_widget(self, value):
        assert isinstance(value, InstanceWidget)
        self._source_instance_widget = value

    @property
    def source_connection_type(self):
        return self._source_connection_type

    @source_connection_type.setter
    def source_connection_type(self, value):
        assert isinstance(value, six.string_types)
        self._source_connection_type = value

    @property
    def source_interface_name(self):
        return self._source_interface_name

    @source_interface_name.setter
    def source_interface_name(self, value):
        assert isinstance(value, six.string_types)
        self._source_interface_name = value

    # Destination Information
    @property
    def dest_instance_widget(self):
        return self._dest_instance_widget

    @dest_instance_widget.setter
    def dest_instance_widget(self, value):
        assert isinstance(value, InstanceWidget)
        self._dest_instance_widget = value

    @property
    def dest_connection_type(self):
        return self._dest_connection_type

    @dest_connection_type.setter
    def dest_connection_type(self, value):
        assert isinstance(value, six.string_types)
        self._dest_connection_type = value

    @property
    def dest_interface_name(self):
        return self._dest_interface_name

    @dest_interface_name.setter
    def dest_interface_name(self, value):
        assert isinstance(value, six.string_types)
        self._dest_interface_name = value

    @property
    def source_pos(self):
        return self._source_pos

    @property
    def source_angle(self):
        return self._source_angle

    def set_source_pos_angle(self, pos, angle):
        assert isinstance(pos, QtCore.QPointF)
        self._source_pos = pos
        self._source_angle = angle

        self.update_path()

    @property
    def dest_pos(self):
        return self._dest_pos

    @property
    def dest_angle(self):
        return self._dest_angle

    def set_dest_pos_angle(self, pos, angle):
        assert isinstance(pos, QtCore.QPointF)
        self._dest_pos = pos
        self._dest_angle = angle

        self.update_path()

    @PropertyInterface.property_widget.getter
    def property_widget(self):
        newWidget = ConnectionPropertyWidget(self)
        return newWidget

    # --- INITIALISATION ---

    def __init__(self, name, con_type, source, source_type, source_inf_name, dest, dest_type, dest_inf_name):
        super(ConnectionWidget, self).__init__()

        self._connection_name = None
        self._connection_name = name
        self._connection_type = None
        self.connection_type = con_type

        self.setToolTip("%s : %s" % (name, con_type) )

        # Get points from attributes of the edge
        self._source_pos = None
        self._dest_pos = None
        self._source_angle = None
        self._dest_angle = None

        self._path = None
        self._hidden = False

        assert isinstance(source, InstanceWidget)
        self._source_instance_widget = source

        self._source_connection_type = None
        self.source_connection_type = source_type

        self._source_interface_name = None
        self.source_interface_name = source_inf_name

        assert isinstance(dest, InstanceWidget)
        self._dest_instance_widget = dest

        self._dest_connection_type = None
        self.dest_connection_type = dest_type

        self._dest_interface_name = None
        self.dest_interface_name = dest_inf_name

        self.source_instance_widget.add_connection(self)
        self.dest_instance_widget.add_connection(self)

    # --- UI FUNCTION ---

    def paint(self, q_painter, style_option, widget=None):
        """
        Deals with the drawing of the connection when asked to paint.
        Realies on self.path to be set
        :param q_painter: QPainter to paint on
        :param style_option: styling options - unused atm
        :param widget: unused atm
        """

        # assert isinstance(style_option, QtWidgets.QStyleOptionGraphicsItem)
        # assert isinstance(widget, QtWidgets.QWidget)

        assert isinstance(q_painter, QtGui.QPainter)

        q_painter.setRenderHint(QtGui.QPainter.Antialiasing)

        if self.source_pos is not None and self.dest_pos is not None:
            pen = QtGui.QPen(QtGui.QColor(66, 66, 66))
            pen.setWidth(2)

            pen_color = pen.color()
            if self.hidden:
                pen_color.setAlphaF(0.2)
            else:
                pen_color.setAlphaF(1)
            pen.setColor(pen_color)

            q_painter.setPen(pen)
            q_painter.drawPath(self.path)
            # q_painter.drawLine(self.source_pos, self.dest_pos)

    def boundingRect(self):
        """
        Calculates bounding rect from current self.path with 2.5 margin
        :return: QRectF
        """

        rect = self.path.boundingRect()
        assert isinstance(rect, QtCore.QRectF)
        rect.adjust(-2.5, -2.5, 2.5, 2.5)

        return rect

    def shape(self):
        """
        Returns the self.path with width = 5
        :return: QPainterPath
        """

        stroker = QtGui.QPainterPathStroker()
        stroker.setWidth(5)
        return stroker.createStroke(self.path)

    # -- Connector drawing --

    def update_path(self):
        """
        Recreates path based on the current (which maybe newly set) source and destination points.
        Relies on: self.source_pos and self.dest_pos to be set.
        """

        # If there is a source and destination point to work with
        if self.source_pos and self.dest_pos:
            self.clear_path()

            # Start at source point
            self.path.moveTo(self.source_pos)

            # For a beizer curve, there are three points that make a curve (for a cubic beizer curve).
            # The middle point is called the control point (since it controls the curvature).
            # There are two curves, one on either side. In the middle, a icon will be drawn if there is space.

            source_control_point = self.get_control_point(self.source_pos, self.dest_pos, self.source_angle)

            destination_control_point = self.get_control_point(self.dest_pos, self.source_pos, self.dest_angle)

            # Find final points for both source and destionation
            if source_control_point != destination_control_point:
                # It doesn't make sense to compare points as < or >, because its a bit ambigious.
                # If we consider * to be source points, and X to be destination point, the following
                # will not occur due to the get_control_point algorithm.
                # * - - - X - - * - - X
                # It would normally look like: * - - - * - - X - - - X

                # Find vector from source to dest
                s_to_d = destination_control_point - source_control_point

                # Get length, and then find source and destination final points.
                # if less than 30 - no enough for icon.
                # otherwise keep 30 pixel space for icon when finding final points
                length = math.sqrt(s_to_d.dotProduct(s_to_d, s_to_d))
                if length < 30:
                    middle_vector = self.change_vector_length(s_to_d, length / 2)

                    source_final_point = source_control_point + middle_vector
                    destination_final_point = destination_control_point - middle_vector
                else:
                    middle_vector = self.change_vector_length(s_to_d, length / 2 - 15)

                    source_final_point = source_control_point + middle_vector
                    destination_final_point = destination_control_point - middle_vector

            else:
                # Make final points the same as control points.
                source_final_point = source_control_point
                destination_final_point = destination_control_point

            # Draw source cubic beizer curve
            self.path.quadTo(source_control_point, source_final_point)

            # Draw icon (if possible)
            self.draw_connector_type(source_final_point, destination_final_point)

            # Draw dest cubic curve
            self.path.moveTo(destination_final_point)
            self.path.quadTo(destination_control_point, self.dest_pos)

            # Let graphicitem know that geometry has changed.
            self.prepareGeometryChange()

    def draw_connector_type(self, source_point, dest_point):
        """
        Draws the icon between two points.
        Expected to be subclassed for different connector types.
        :param source_point: QPointF - the starting point
        :param dest_point: QPointF - the ending point
        :return:
        """

        assert isinstance(source_point, QtCore.QPointF)
        assert isinstance(dest_point, QtCore.QPointF)

        self.path.moveTo(source_point)
        self.path.lineTo(dest_point)

    # --- EVENTS ---

    def mousePressEvent(self, mouse_event):
        """
        Deals with mouse pressed events. Does nothing atm.
        :param mouse_event: QGraphicsSceneMouseEvent
        """
        assert isinstance(mouse_event, QtWidgets.QGraphicsSceneMouseEvent)
        super(ConnectionWidget, self).mousePressEvent(mouse_event)

    # --- HELPER FUNCTIONS ---

    @staticmethod
    def change_vector_length(old_point, new_length):
        """
        Helper function to change the length of a vector
        :param old_point: The current vector
        :param new_length: The new length of the vector
        :return: QPointF - new vector with the new length
        """

        assert isinstance(old_point, QtCore.QPointF)
        old_length = math.sqrt(old_point.x() * old_point.x() + old_point.y() * old_point.y())

        if old_length == 0:
            # It doesn't make sense to extend or shorten a zero vector
            return old_point

        new_point = QtCore.QPointF((old_point.x() * new_length) / old_length, (old_point.y() * new_length) / old_length)
        return new_point

    @staticmethod
    def get_control_point(source_pos, dest_pos, angle):
        """
        Get the middle point of the cubic beizer curve.
        To get the source control point - pass in source point as source_pos and destination point as dest_pos
        To get the dest control porint - pass in destination point as source_pos and source point as source_pos
        :param source_pos: QPointF - source point
        :param dest_pos: QPointF - destination point
        :param angle: int - the distance that the final point has to be, from the straight line
        :return: QPointF - the middle control point
        """

        assert isinstance(source_pos, QtCore.QPointF)
        assert isinstance(dest_pos, QtCore.QPointF)

        # Get vector from start to end
        s_to_d = dest_pos - source_pos
        assert isinstance(s_to_d, QtCore.QPointF)

        normal_length = 10

        # If the s_to_d length is less than 20, then set normal_length to half s_to_d length
        # This will mean that source and destination control points are the same
        if (math.sqrt(s_to_d.dotProduct(s_to_d, s_to_d)) / 2) < normal_length:
            normal_length = math.sqrt(s_to_d.dotProduct(s_to_d, s_to_d)) / 2

        s_to_d = ConnectionWidget.change_vector_length(s_to_d, normal_length)
        perpend_vector = QtCore.QPointF(-s_to_d.y(), s_to_d.x())
        perpend_vector = ConnectionWidget.change_vector_length(perpend_vector, angle)

        source_control_point = source_pos + s_to_d + perpend_vector

        return source_control_point

    def delete(self):
        """
        Before removing the connection, make sure to call this function.
        :return:
        """

        # TODO: Delete connection from source & destination
        self.source_instance_widget.remove_connection(self)
        self.dest_instance_widget.remove_connection(self)

class DataportWidget(ConnectionWidget):
    """
    Subclass of ConnectionWidget, which deals with the drawing of the Dataport icon
    for the connection type.
    """

    # Draws a rectangle
    def draw_connector_type(self, source_point, dest_point):
        assert isinstance(source_point, QtCore.QPointF)
        assert isinstance(dest_point, QtCore.QPointF)

        if source_point == dest_point:
            return

        s_to_d = dest_point - source_point
        assert isinstance(s_to_d, QtCore.QPointF)

        # Convert s_to_d to perpendicular vector
        old_x = s_to_d.x()
        s_to_d.setX(-s_to_d.y())
        s_to_d.setY(old_x)

        new_vector = self.change_vector_length(s_to_d, 10)
        top_left = source_point + new_vector
        top_right = dest_point + new_vector
        bottom_left = source_point - new_vector
        bottom_right = dest_point - new_vector

        self.path.moveTo(top_left)
        self.path.lineTo(top_right)
        self.path.lineTo(bottom_right)
        self.path.lineTo(bottom_left)
        self.path.lineTo(top_left)

class ProcedureWidget(ConnectionWidget):
    """
    Subclass of ConnectionWidget, which deals with the drawing of the Procedure icon
    for the connection type.
    """

    # Draws a circle
    def draw_connector_type(self, source_point, dest_point):
        assert isinstance(source_point, QtCore.QPointF)
        assert isinstance(dest_point, QtCore.QPointF)

        if source_point == dest_point:
            return

        s_to_d = dest_point - source_point
        assert isinstance(s_to_d, QtCore.QPointF)
        s_to_d = self.change_vector_length(s_to_d, 5)

        start_point = source_point + s_to_d
        end_point = dest_point - s_to_d

        self.path.moveTo(source_point)
        self.path.lineTo(start_point)

        centre_point = self.change_vector_length(s_to_d, 14) + start_point

        new_vector = QtCore.QPointF(-s_to_d.y(), s_to_d.x())
        new_vector = self.change_vector_length(new_vector, 14)
        arc_start_point = centre_point + new_vector

        self.path.moveTo(arc_start_point)

        top_left = centre_point - QtCore.QPointF(14, 14)
        bottom_right = centre_point + QtCore.QPointF(14, 14)
        rect = QtCore.QRectF(top_left, bottom_right)

        straight_point = QtCore.QPointF(1, 0)

        start_straight_dot_product = new_vector.dotProduct(new_vector, straight_point)
        perpend_length = math.sqrt(new_vector.x() * new_vector.x() + new_vector.y() * new_vector.y())
        straight_length = math.sqrt(straight_point.x() * straight_point.x() + straight_point.y() * straight_point.y())

        start_angle = math.degrees(math.acos(start_straight_dot_product / (perpend_length * straight_length)))

        if new_vector.y() > 0:
            start_angle = 360 - start_angle

        self.path.arcTo(rect, start_angle, -180)

        top_left = centre_point - QtCore.QPointF(6, 6)
        bottom_right = centre_point + QtCore.QPointF(6, 6)
        rect = QtCore.QRectF(top_left, bottom_right)

        self.path.addEllipse(rect)

        self.path.moveTo(end_point)
        self.path.lineTo(dest_point)

class EventWidget(ConnectionWidget):
    """
    Subclass of ConnectionWidget, which deals with the drawing of the Event icon
    for the connection type.
    """

    # Draws a triangle
    def draw_connector_type(self, source_point, dest_point):
        assert isinstance(source_point, QtCore.QPointF)
        assert isinstance(dest_point, QtCore.QPointF)

        if source_point == dest_point:
            return

        s_to_d = dest_point - source_point
        assert isinstance(s_to_d, QtCore.QPointF)
        s_to_d = self.change_vector_length(s_to_d, 5)

        start_point = source_point + s_to_d
        end_point = dest_point - s_to_d

        new_vector = QtCore.QPointF(-s_to_d.y(), s_to_d.x())
        new_vector = self.change_vector_length(new_vector, 10)

        self.path.moveTo(source_point)
        self.path.lineTo(start_point)

        top_left = start_point + new_vector
        bottom_left = start_point - new_vector

        s_to_d = self.change_vector_length(s_to_d, 14)

        first_end = start_point + s_to_d

        self.path.moveTo(top_left)
        self.path.lineTo(bottom_left)
        self.path.lineTo(first_end)
        self.path.lineTo(top_left)

        s_to_d = self.change_vector_length(s_to_d, 6)
        top_left = top_left + s_to_d
        bottom_left = bottom_left + s_to_d

        self.path.moveTo(top_left)
        self.path.lineTo(end_point)
        self.path.lineTo(bottom_left)

        self.path.moveTo(end_point)

        self.path.lineTo(dest_point)
