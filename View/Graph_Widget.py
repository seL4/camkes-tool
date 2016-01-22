#!/usr/bin/env python
# -*- coding: utf-8 -*-

from PyQt5 import QtWidgets, QtGui, QtCore

from Connection_Widget import ConnectionWidget
from Instance_Widget import InstanceWidget

class GraphWidget(QtWidgets.QGraphicsView):

    @property
    def connection_widgets(self):
        # Lazy instantiation
        if self._connection_widgets is None:
            self._connection_widgets = []
        return self._connection_widgets

    # @property
    # def instance_widgets(self):
    #     # Lazy instantiation
    #     if self._instance_widgets is None:
    #         self._instance_widgets = []
    #     return self._instance_widgets
    #
    # @instance_widgets.setter
    # def instance_widgets(self, value):
    #     assert isinstance(value, list)
    #     self._instance_widgets = value

    @property
    def zoom_in_button(self):
        if self._zoom_in is None:
            self._zoom_in  = QtWidgets.QPushButton("Zoom In", self)
            self._zoom_in.setAutoRepeat(True)
            self._zoom_in.clicked.connect(self.zoom_in)
            self.update_outer_ui()
        return self._zoom_in

    @property
    def zoom_out_buttom(self):
        if self._zoom_out is None:
            self._zoom_out = QtWidgets.QPushButton("Zoom Out", self)
            self._zoom_out.setAutoRepeat(True)
            self._zoom_out.clicked.connect(self.zoom_out)
            self.update_outer_ui()
        return self._zoom_out

    def __init__(self):
        super(GraphWidget, self).__init__()
        self._connection_widgets = None
        self._instance_widgets = None
        self._zoom_in = None
        self._zoom_out = None

        scene = QtWidgets.QGraphicsScene(self)
        scene.setItemIndexMethod(QtWidgets.QGraphicsScene.NoIndex) #TODO: Not sure if this is necessary
        scene.setSceneRect(0,0,500,500) # Random size, should be given when controller renders

        self.setScene(scene)

        self.setMinimumSize(500,500)

        self.update_outer_ui()

    def add_instance_widget(self, new_widget, x_pos, y_pos):

        assert isinstance(new_widget, InstanceWidget)

        if new_widget not in [x for x in self.scene().items()
                              if isinstance(x, InstanceWidget)]:
            # set parent widget of new widget to be self
            self.scene().addItem(new_widget)
            new_widget.setZValue(5)
            new_widget.widget_moved.connect(self.instance_widget_moved)

        new_widget.setPos(x_pos - (new_widget.preferredSize().width()/2), y_pos - (new_widget.preferredSize().height()/2))


    # def drawBackground(self, q_painter, rectangle):
    #     super(GraphWidget, self).drawBackground(q_painter, rectangle)
    #
    #     # Loop through all connectors
    #     for connector in self.connection_widgets:
    #         assert isinstance(connector, ConnectionWidget)
    #         connector.draw_connection(q_painter)

    def remove_instance_widget(self, old_widget):
        raise NotImplementedError

    def add_connection_widget(self, new_connection):
        """

        :type new_connection: ConnectionWidget
        """
        assert isinstance(new_connection, ConnectionWidget)
        self.connection_widgets.append(new_connection)

        self.scene().addItem(new_connection)
        new_connection.setZValue(1)

    def clear_connection_widgets(self):

        scene = self.scene()
        assert isinstance(scene, QtWidgets.QGraphicsScene)

        for connection in self.connection_widgets:
            scene.removeItem(connection)
            self.connection_widgets.remove(connection)
            del connection


    # Set UI Functions
    def setViewGeometry(self, size_x, size_y):
        print "Set view geometry called"
        self.scene().setSceneRect(0,0,size_x, size_y)
        self.setMinimumSize(500, 500)
        
    def mousePressEvent(self, mouse_event):
        super(GraphWidget, self).mousePressEvent(mouse_event)

        assert isinstance(mouse_event, QtGui.QMouseEvent)
        print "\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\tgraph widget - clicked at: " + str(self.mapToScene(mouse_event.pos()))

    def resizeEvent(self, resize_event):
        assert isinstance(resize_event, QtGui.QResizeEvent)
        super(GraphWidget, self).resizeEvent(resize_event)

        self.update_outer_ui()

    def update_outer_ui(self):
        bottom_corner = self.pos() + QtCore.QPoint(self.width(), self.height())

        zoom_in_position = bottom_corner - QtCore.QPoint(self.zoom_in_button.sizeHint().width(),
                                                         self.zoom_in_button.sizeHint().height()) \
                           - QtCore.QPoint(20, 20)

        self.zoom_in_button.move(zoom_in_position)
        self.zoom_in_button.show()

        zoom_out_position = zoom_in_position - QtCore.QPoint(self.zoom_out_buttom.sizeHint().width() + 20, 0)

        self.zoom_out_buttom.move(zoom_out_position)
        self.zoom_out_buttom.show()

    def instance_widget_moved(self):
        widget = self.sender()
        assert isinstance(widget, InstanceWidget)



        # print "Widget moved: " + str(widget.scenePos())

        rect = self.sceneRect()
        assert isinstance(rect, QtCore.QRectF)

        print "Rect before: " + str(rect)

        # if rect.x() > widget.scenePos().x():
        #     rect.setX(widget.scenePos().x())
        #
        # if rect.y() > widget.scenePos().y():
        #     rect.setY(widget.scenePos().y())
        #
        # if rect.right() < (widget.scenePos().x() + widget.boundingRect().width()):
        #     rect.setRight((widget.scenePos().x() + widget.boundingRect().width()))
        #
        # if rect.bottom() < (widget.scenePos().y() + widget.boundingRect().height()):
        #     rect.setBottom((widget.scenePos().y() + widget.boundingRect().height()))
        #
        # print "Rect after: " + str(rect)

        smallest_x = 0
        smallest_y = 0
        largest_x = 0
        largest_y = 0

        for instance_widget in [x for x in self.scene().items() if isinstance(x, InstanceWidget)]:
            assert isinstance(instance_widget, InstanceWidget)

            if instance_widget.scenePos().x() < smallest_x:
                smallest_x = instance_widget.scenePos().x()

            if instance_widget.scenePos().y() < smallest_y:
                smallest_y = instance_widget.scenePos().y()

            bottom_corner = instance_widget.scenePos() + QtCore.QPointF(instance_widget.boundingRect().width(),
                                                                        instance_widget.boundingRect().height())
            print "Bottom Corner" + str(bottom_corner)

            if largest_x < bottom_corner.x():
                largest_x = bottom_corner.x()

            if largest_y < bottom_corner.y():
                largest_y = bottom_corner.y()

        print str(smallest_x) + "," + str(smallest_y) + "," + str(largest_x) + "," + str(largest_y)
        new_rect = QtCore.QRectF(smallest_x, smallest_y, largest_x-smallest_x, largest_y-smallest_y)

        print "Rect after: " + str(new_rect)


        self.setSceneRect(new_rect)


    def zoom_in(self):
        print "Zoom in"
        self.scale(1.1,1.1)

    def zoom_out(self):
        print "Zoom out"
        self.scale(0.9,0.9)

    # def mouseMoveEvent(self, mouse_event):
    #     print "graph widget " + str(mouse_event.pos())