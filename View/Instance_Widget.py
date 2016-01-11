#!/usr/bin/env python
# -*- coding: utf-8 -*-

import six

from PyQt5 import QtGui, QtWidgets, QtCore
from camkes.ast import *

# TODO: Make widget totally independent of instance_object, and make controller force AST_creator to search it up everytime,
# TODO: Button for component details
#       Use instance.name as identifier.

class InstanceWidget(QtWidgets.QFrame):
    @property
    def instance_object(self):
        return self._instance_object

    @instance_object.setter
    def instance_object(self, value):
        assert isinstance(value, Instance)
        self._instance_object = value

    @property
    def instance_name(self):
        if self._instance_name is None:
            raise Exception # TODO make subclass of exception, catch and show a dialog
        return self._instance_name

    @instance_name.setter
    def instance_name(self, value):
        assert isinstance(value, six.string_types)
        self._instance_name = value
        self.update_ui()

    @property
    def preferred_point(self):
        return self._preferred_point

    @preferred_point.setter
    def preferred_point(self, value):
        assert isinstance(value, QtCore.QPointF)
        self._preferred_point = value

    @property
    def proxy_widget(self):
        return self._proxy_widget

    @proxy_widget.setter
    def proxy_widget(self, value):
        assert isinstance(value, QtWidgets.QGraphicsProxyWidget)
        self._proxy_widget = value

    # Signals & Slots
    open_component_info = QtCore.pyqtSignal(Instance)
    widget_moved = QtCore.pyqtSignal()

    def __init__(self, instance_object, preferred_point=None):
        super(InstanceWidget, self).__init__()
        # Model

        self._instance_object = instance_object
        self._instance_name = instance_object.name
        self._proxy_widget = None
        self._preferred_point = preferred_point

        # GUI
        self.setFrameStyle(QtWidgets.QFrame.Panel)

        layout = QtWidgets.QVBoxLayout()

        self.setLayout(layout)

        self.update_ui()

    def update_ui(self):

        self.clear_canvas()

        layout = self.layout()
        assert isinstance(layout, QtWidgets.QVBoxLayout)

        if self.instance_object:
            string = self.instance_object.name + ": " + self.instance_object.type.name
            new_label = QtWidgets.QLabel(string)

            layout.addWidget(new_label)

            if self.instance_object.type.control:
                layout.addWidget(QtWidgets.QLabel("control;"))

            if self.instance_object.type.hardware:
                layout.addWidget(QtWidgets.QLabel("hardware;"))

    def mousePressEvent(self, mouse_event):
        # Change to must press a button to open component info
        self.open_component_info.emit(self.instance_object)

    previous_position = None

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
        assert isinstance(layout, QtWidgets.QVBoxLayout)

        next_widget = layout.takeAt(0)
        while next_widget is not None:
            del next_widget
            next_widget = layout.takeAt(0)
