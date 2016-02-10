#!/usr/bin/env python
# -*- coding: utf-8 -*-

import math, six

from PyQt5 import QtGui, QtWidgets, QtCore

from Instance_Widget import InstanceWidget


class ConnectionWidget(QtWidgets.QGraphicsItem):

    @property
    def name(self):
        return self._connection_name

    @name.setter
    def name(self, value):
        assert isinstance(value, six.string_types)
        self._connection_name = value

    @property
    def connection_type(self):
        return self._connection_type

    @connection_type.setter
    def connection_type(self, value):
        assert isinstance(value, six.string_types)
        self._connection_type = value

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

    # @source_pos.setter
    # def source_pos(self, value):
    #     print "set2"
    #     self._source_pos = value
    #     self.update_path()

    @property
    def source_angle(self):
        return self._source_angle

    # @source_angle.setter
    # def source_angle(self, value):
    #     self._source_angle = value

    def set_source_pos_angle(self, pos, angle):
        assert isinstance(pos, QtCore.QPointF)
        self._source_pos = pos
        self._source_angle = angle

        self.update_path()

    @property
    def dest_pos(self):
        return self._dest_pos

    # @dest_pos.setter
    # def dest_pos(self, value):
    #     print "set"
    #     self._dest_pos = value
    #     self.update_path()

    @property
    def dest_angle(self):
        return self._dest_angle

    # @dest_angle.setter
    # def dest_angle(self, value):
    #     self._dest_angle = value

    def set_dest_pos_angle(self, pos, angle):
        assert isinstance(pos, QtCore.QPointF)
        self._dest_pos = pos
        self._dest_angle = angle

        self.update_path()

    def update_path(self):

        if self.source_pos and self.dest_pos:
            self.clear_path()

            # print "Making path - source is :" + str(self.source_pos) + " destination is:" +str(self.dest_pos) + " angle is:" + str(self.source_angle)

            self.path.moveTo(self.source_pos)

            source_control_point = self.get_control_point(self.source_pos, self.dest_pos, self.source_angle)

            destination_control_point = self.get_control_point(self.dest_pos, self.source_pos, self.dest_angle)

            if source_control_point != destination_control_point:
                # Draw connection stuff

                s_to_d = destination_control_point - source_control_point

                length = math.sqrt(s_to_d.dotProduct(s_to_d, s_to_d))
                if length < 30:
                    middle_vector = self.change_vector_length(s_to_d,length/2)

                    source_final_point = source_control_point + middle_vector
                    destination_final_point = destination_control_point - middle_vector
                else:
                    middle_vector = self.change_vector_length(s_to_d,length/2 - 15)

                    source_final_point = source_control_point + middle_vector
                    destination_final_point = destination_control_point - middle_vector

            else:
                source_final_point = source_control_point
                destination_final_point = destination_control_point

            self.path.quadTo(source_control_point, source_final_point)

            self.draw_connector_type(source_final_point, destination_final_point)

            self.path.moveTo(destination_final_point)

            self.path.quadTo(destination_control_point, self.dest_pos)

            self.prepareGeometryChange()

    def draw_connector_type(self, source_point, dest_point):
        assert isinstance(source_point, QtCore.QPointF)
        assert isinstance(dest_point, QtCore.QPointF)

        self.path.moveTo(source_point)
        self.path.lineTo(dest_point)

    @staticmethod
    def change_vector_length(old_point, new_length):
        assert isinstance(old_point, QtCore.QPointF)
        old_length = math.sqrt(old_point.x()*old_point.x() + old_point.y()*old_point.y())

        if old_length == 0:
            # It doesn't make sense to extend or shorten a zero vector
            return old_point

        new_point = QtCore.QPointF((old_point.x() * new_length) / old_length, (old_point.y()*new_length)/old_length)
        return new_point

    @staticmethod
    def get_control_point(source_pos, dest_pos, angle):

        assert isinstance(source_pos, QtCore.QPointF)
        assert isinstance(dest_pos, QtCore.QPointF)

        # --- To get control point. ---
        # # Get vector from source to destination
        # s_to_d = dest_pos - source_pos
        # assert isinstance(s_to_d, QtCore.QPointF)
        # print "\ts_to_d is " + str(s_to_d)
        # # Rotate by angle degrees:
        # # x' = xcos(a) - ysin(a)
        # # y' = xsin(a) - ycos(a)
        # new_x = s_to_d.x() * math.cos(math.radians(angle)) - \
        #         s_to_d.y() * math.sin(math.radians(angle))
        # new_y = s_to_d.x() * math.sin(math.radians(angle)) + \
        #         s_to_d.y() * math.cos(math.radians(angle))
        # print "\trotation to " + str(new_x) + "," + str(new_y)
        #
        # # And then ensure this vector's cos(a) is of length 10 (normal_length)
        # # x'' = x' * (10/cos(a))/|v|
        # # y'' = y' * (10/cos(a))/|v|
        #
        # normal_length = 10
        #
        # if (math.sqrt(QtCore.QPointF.dotProduct(s_to_d, s_to_d)) / 2) < normal_length:
        #     normal_length = math.sqrt(QtCore.QPointF.dotProduct(s_to_d, s_to_d)) / 2
        #
        # length = math.cos(math.radians(angle)) * math.sqrt(new_x * new_x + new_y * new_y)
        # new_x = (new_x * normal_length) / length
        # new_y = (new_y * normal_length) / length
        #
        # print "\t normalised to " + str(new_x) + "," + str(new_y)
        # source_control_point = QtCore.QPointF(new_x, new_y)
        # source_control_point += source_pos
        # print "\t final point is " + str(source_control_point)


        s_to_d = dest_pos - source_pos
        assert isinstance(s_to_d, QtCore.QPointF)
        # print "\ts_to_d is " + str(s_to_d)

        normal_length = 10

        if (math.sqrt(s_to_d.dotProduct(s_to_d, s_to_d)) / 2) < normal_length:
            normal_length = math.sqrt(s_to_d.dotProduct(s_to_d, s_to_d)) / 2

        s_to_d = ConnectionWidget.change_vector_length(s_to_d, normal_length)
        perpend_vector = QtCore.QPointF(-s_to_d.y(), s_to_d.x())
        perpend_vector = ConnectionWidget.change_vector_length(perpend_vector, angle)

        source_control_point = source_pos + s_to_d + perpend_vector

        return source_control_point


    def __init__(self, name, con_type, source, source_type, source_inf_name, dest, dest_type, dest_inf_name):
        super(ConnectionWidget, self).__init__()

        self._connection_name = None
        self._connection_name = name
        self._connection_type = None
        self.connection_type = con_type

        # Get points from attributes of the edge
        self._source_pos = None
        self._dest_pos = None
        self._source_angle = None
        self._dest_angle = None

        self._path = None

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

    def paint(self, q_painter, style_option , widget=None):

        # assert isinstance(style_option, QtWidgets.QStyleOptionGraphicsItem)
        # assert isinstance(widget, QtWidgets.QWidget)

        assert isinstance(q_painter, QtGui.QPainter)

        # stroker = QtGui.QPainterPathStroker()
        # stroker.setWidth(5)
        # self.path.addPath(stroker.createStroke(self.path))

        # q_painter.drawPath(self.path)

        q_painter.setRenderHint(QtGui.QPainter.Antialiasing)

        if self.source_pos is not None and self.dest_pos is not None:
            pen = QtGui.QPen(QtGui.QColor(66,66,66))
            pen.setWidth(2)

            q_painter.setPen(pen)
            q_painter.drawPath(self.path)
            # q_painter.drawLine(self.source_pos, self.dest_pos)

    def boundingRect(self):
        rect = self.path.boundingRect()
        assert isinstance(rect, QtCore.QRectF)
        rect.adjust(-2.5,-2.5,2.5,2.5)

        return rect

    def shape(self):
        stroker = QtGui.QPainterPathStroker()
        stroker.setWidth(5)
        return stroker.createStroke(self.path)

    def mousePressEvent(self, mouse_event):
        assert isinstance(mouse_event, QtWidgets.QGraphicsSceneMouseEvent)
        print self.name + " clicked (edge)"

    def delete(self):
        # TODO: Delete connection from source & destination
        self.source_instance_widget.remove_connection(self)
        self.dest_instance_widget.remove_connection(self)
        print "\t\t\t\t\t\tdeleted connection_widget"

    # Method using QPainter to draw the edge points, spline
    # def draw_connection(self, q_painter):
    #     assert isinstance(q_painter, QtGui.QPainter)
    #     q_painter.drawPath(self.path)
    #
    #     '''
    #     color = QtGui.QColor(0,0,0)
    #     pen = q_painter.pen()
    #     pen.setColor(color)
    #     q_painter.setPen(pen)
    #
    #     for point in self.edge_points:
    #
    #         color = q_painter.pen().color()
    #         print "Before: " + str(color.red()) + " " + str(color.green()) + " " + str(color.blue())
    #         color.setRed(color.red()+30)
    #         print str(color.red()) + " " + str(color.green()) + " " + str(color.blue())
    #
    #         pen = q_painter.pen()
    #         pen.setColor(color)
    #         q_painter.setPen(pen)
    #
    #         color = q_painter.pen().color()
    #         print "after" + str(color.red()) + " " + str(color.green()) + " " + str(color.blue())
    #
    #         q_painter.drawPoint(point[0], point[1])
    #         q_painter.fillRect(QtCore.QRect(point[0], point[1], 4,4), color)
    #     '''


class DataportWidget(ConnectionWidget):

    def draw_connector_type(self, source_point, dest_point):
        assert isinstance(source_point, QtCore.QPointF)
        assert isinstance(dest_point, QtCore.QPointF)

        if source_point == dest_point:
            return

        s_to_d = dest_point - source_point
        assert isinstance(s_to_d, QtCore.QPointF)

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


class EventWidget(ConnectionWidget):

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

        straight_point = QtCore.QPointF(1,0)

        start_straight_dot_product = new_vector.dotProduct(new_vector, straight_point)
        perpend_length = math.sqrt(new_vector.x()*new_vector.x() + new_vector.y()*new_vector.y())
        straight_length = math.sqrt(straight_point.x()*straight_point.x() + straight_point.y()*straight_point.y())

        start_angle = math.degrees(math.acos(start_straight_dot_product/(perpend_length*straight_length)))

        if new_vector.y() > 0:
            start_angle = 360-start_angle

        self.path.arcTo(rect, start_angle, -180)

        top_left = centre_point - QtCore.QPointF(6, 6)
        bottom_right = centre_point + QtCore.QPointF(6, 6)
        rect = QtCore.QRectF(top_left, bottom_right)

        self.path.addEllipse(rect)

        self.path.moveTo(end_point)
        self.path.lineTo(dest_point)


class ProcedureWidget(ConnectionWidget):

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
