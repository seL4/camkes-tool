#!/usr/bin/env python
# -*- coding: utf-8 -*-

from PyQt5 import QtWidgets, QtGui

from Connection_Widget import ConnectionWidget


class GraphWidget(QtWidgets.QGraphicsView):

    @property
    def connection_widgets(self):
        # Lazy instantiation
        if self._connection_widgets is None:
            self._connection_widgets = []
        return self._connection_widgets

    def add_connection_widget(self, new_connection):
        """

        :type new_connection: ConnectionWidget
        """
        assert isinstance(new_connection, ConnectionWidget)
        self.connection_widgets.append(new_connection)

        self.scene().addItem(new_connection)

    def __init__(self):
        super(GraphWidget, self).__init__()
        self._connection_widgets = None

        scene = QtWidgets.QGraphicsScene(self)
        scene.setItemIndexMethod(QtWidgets.QGraphicsScene.NoIndex) #TODO: Not sure if this is necessary
        scene.setSceneRect(0,0,500,500) # Random size, should be given when controller renders

        self.setScene(scene)

        self.setMinimumSize(500,500)

    def add_instance_widget(self, new_widget, x_pos, y_pos):

        assert isinstance(new_widget, QtWidgets.QWidget)

        if new_widget not in self.scene().items():
            # set parent widget of new widget to be self
            self.scene().addWidget(new_widget)

        new_widget.move(x_pos - (new_widget.sizeHint().width()/2), y_pos - (new_widget.sizeHint().height()/2))

    # def drawBackground(self, q_painter, rectangle):
    #     super(GraphWidget, self).drawBackground(q_painter, rectangle)
    #
    #     # Loop through all connectors
    #     for connector in self.connection_widgets:
    #         assert isinstance(connector, ConnectionWidget)
    #         connector.draw_connection(q_painter)

        # TODO: Possible feature, only update the rect given in QPaintEvent

    # Set UI Functions
    def setViewGeometry(self, size_x, size_y):
        self.scene().setSceneRect(0,0,size_x, size_y)
        self.setMinimumSize(size_x, size_y)