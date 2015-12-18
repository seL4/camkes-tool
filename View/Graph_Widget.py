#!/usr/bin/env python
# -*- coding: utf-8 -*-

from PyQt5 import QtWidgets, QtGui

from Connection_Widget import ConnectionWidget


class GraphWidget(QtWidgets.QFrame):

    @property
    def connection_widgets(self):
        # Lazy instantiation
        if self._connection_widgets is None:
            self._connection_widgets = []
        return self._connection_widgets

    def add_connection_widget(self, new_connection):
        assert isinstance(new_connection, ConnectionWidget)
        self.connection_widgets.append(new_connection)

    def __init__(self):
        super(GraphWidget, self).__init__()
        self._connection_widgets = None

    def add_instance_widget(self, new_widget, x_pos, y_pos):

        # set parent widget of new widget to be self
        # raise NotImplementedError

        assert isinstance(new_widget, QtWidgets.QWidget)
        new_widget.setParent(self)
        self.move_instance_widget(new_widget, x_pos, y_pos)

    def move_instance_widget(self, widget, new_x_pos, new_y_pos):
        # Takes center positions of widget

        # TODO: Check if widget is a child.

        # Move widget to the middle
        widget.move(new_x_pos - (widget.sizeHint().width()/2), new_y_pos - (widget.sizeHint().height()/2))
        pass

    def paintEvent(self, QPaintEvent):
        super(GraphWidget, self).paintEvent(QPaintEvent)

        q_painter = QtGui.QPainter()
        q_painter.begin(self)

        # Loop through all connectors
        for connector in self.connection_widgets:
            assert isinstance(connector, ConnectionWidget)
            connector.draw_connection(q_painter)

        q_painter.end()

        # TODO: Possible feature, only update the rect given in QPaintEvent

