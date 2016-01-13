#!/usr/bin/env python
# -*- coding: utf-8 -*-

import six

from PyQt5 import QtGui, QtWidgets, QtCore
from camkes.ast import *

# TODO: Make widget totally independent of instance_object, and make controller force AST_creator to search it up everytime,
# TODO: Button for component details
#       Use instance.name as identifier.


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
            raise Exception  # TODO make subclass of exception, catch and show a dialog
        return self._instance_name

    @instance_name.setter
    def instance_name(self, value):
        assert isinstance(value, six.string_types)
        self._instance_name = value
        self.update_ui()

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

    # Signals & Slots
    open_component_info = QtCore.pyqtSignal(Instance)
    widget_moved = QtCore.pyqtSignal()

    def __init__(self, instance_object, preferred_point=None):
        super(InstanceWidget, self).__init__()
        # Model

        self._instance_object = instance_object
        self._instance_name = instance_object.name
        self._preferred_point = preferred_point
        self._pinned = False
        self._velocity = None

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

        if self.instance_object:
            string = self.instance_object.name + ": " + self.instance_object.type.name
            new_label = QtWidgets.QLabel(string)

            proxy_widget = QtWidgets.QGraphicsProxyWidget()
            proxy_widget.setWidget(new_label)

            layout.addItem(proxy_widget)

            if self.instance_object.type.control:
                proxy_widget = QtWidgets.QGraphicsProxyWidget()
                proxy_widget.setWidget(QtWidgets.QLabel("control;"))
                layout.addItem(proxy_widget)

            if self.instance_object.type.hardware:
                proxy_widget = QtWidgets.QGraphicsProxyWidget()
                proxy_widget.setWidget(QtWidgets.QLabel("hardware;"))
                layout.addItem(proxy_widget)

    def mousePressEvent(self, mouse_event):
        # Change to must press a button to open component info
        self.open_component_info.emit(self.instance_object)

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

        if layout.count() <= 0:
            return

        next_widget = layout.itemAt(0)
        while next_widget is not None:
            # del next_widget
            next_widget = layout.removeAt(0)
