#!/usr/bin/env python
# -*- coding: utf-8 -*-

import math, six

from PyQt5 import QtGui, QtWidgets, QtCore

# TODO: Change
import pydotplus as Pydot

from Model import Common
from Instance_Widget import InstanceWidget


# TODO: Make connectionWidget totally independent of connection_object. Have links to the nodes that its connecting.
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
    def edge(self):
        return self._edge

    @edge.setter
    def edge(self, value):
        assert isinstance(value, Pydot.Edge)
        self._edge = value
        edge_attributes = value.get_attributes()
        edge_points = Common.extract_numbers(edge_attributes['pos'])
        self.edge_points = edge_points


    @property
    def edge_points(self):
        return self._edge_points

    @edge_points.setter
    def edge_points(self, value):
        assert isinstance(value, list)
        # TODO: Change from edge point to tuple
        # TODO: Different method
        if len(value) >= 2:
            assert isinstance(value[1], tuple)
            self.path.moveTo(value[1][0], value[1][1])

        if len(value) >= 3:
            for point in value[2:]:
                self.path.lineTo(point[0], point[1])

        assert isinstance(value[0], tuple)
        self.path.lineTo(value[0][0], value[0][1])

        # assert isinstance(value[-1], tuple)
        # self.path.lineTo(value[-1][0], value[-1][1])

        self._edge_points = value

        self.prepareGeometryChange()

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

    connection_object = None # TODO: take out

    def __init__(self, name, con_type, source, source_type, source_inf_name, dest, dest_type, dest_inf_name, edge=None):
        super(ConnectionWidget, self).__init__()

        self._connection_name = None
        self._connection_name = name
        self._connection_type = None
        self.connection_type = con_type

        self._edge = None
        self._edge_points = None
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

        # Get points from attributes of the edge
        if edge:
            self.edge = edge


    def paint(self, q_painter, style_option , widget=None):

        # assert isinstance(style_option, QtWidgets.QStyleOptionGraphicsItem)
        # assert isinstance(widget, QtWidgets.QWidget)

        assert isinstance(q_painter, QtGui.QPainter)

        # stroker = QtGui.QPainterPathStroker()
        # stroker.setWidth(5)
        # self.path.addPath(stroker.createStroke(self.path))

        q_painter.drawPath(self.path)

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

    def __del__(self):
        # TODO: Delete connection from source & destination
        self.source_instance_widget.remove_connection(self)
        self.dest_instance_widget.remove_connection(self)
        print "deleted connection_widget"
        
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
