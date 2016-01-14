#!/usr/bin/env python
# -*- coding: utf-8 -*-

import sys, math

# TODO: should be able to remove this, as controller shouldn't be dependent on graphics library (that's the goal)
from PyQt5 import QtWidgets, QtGui, QtCore, QtSvg
# install python-pyqt5.qtsvg
# install libqt5svg5-dev

from pygraphviz import *
# NOTES:    pip install pygraphviz --install-option="--include-path=/usr/include/graphviz"
#                                  --install-option="--library-path=/usr/lib/graphviz/"
#           http://stackoverflow.com/questions/32885486/pygraphviz-importerror-undefined-symbol-agundirected
# from graphviz import Graph

# TODO: ACtually maybe not, double check
# WARNING NEEED TO INSTALLL python-gi-cairo
# sudo apt-get install python-gi-cairo

# TODO: use pydotplus properly, change in connection_widget too
import pydotplus as Pydot

from Controller.base_controller import Controller
from Model.AST_Model import ASTModel
from Model import Common
from View.Graph_Widget import GraphWidget
from View.Connection_Widget import ConnectionWidget
from View.Instance_Widget import InstanceWidget
from View.Component_Window import ComponentWindow

# TODO: Add camkes tools to path, or make an init file or something
from camkes.ast.base import ASTObject
from camkes.ast.liftedast import LiftedAST
from camkes.ast import *

# TODO: Move some of the controller stuff, like make a graph from ast into graph widget and rendering as well.

class GraphController(QtWidgets.QMainWindow):

    # Constants
    _connection_length = 50  # pixels
    _max_velocity_for_widget_animation = 2000

    # Default root_widget is a GraphWidget
    @property
    def root_widget(self):
        # Lazy Instantiation
        if self._root_widget is None:
            self._root_widget = GraphWidget()
        return self._root_widget

    @root_widget.setter
    def root_widget(self, value):
        assert isinstance(value, GraphWidget)
        self._root_widget = value

    @property
    def component_widget(self):
        if self._component_widget is None:
            self._component_widget = ComponentWindow(None)
            self._component_dock_widget = QtWidgets.QDockWidget("Component Info")
            self._component_dock_widget.setWidget(self._component_widget)
            self.addDockWidget(QtCore.Qt.BottomDockWidgetArea, self._component_dock_widget)
        self._component_dock_widget.setVisible(True)
        return self._component_widget

    @property
    def ast(self):
        return self._ast

    @ast.setter
    def ast(self, value):
        assert isinstance(value, LiftedAST)
        self._ast = value

    @property
    def widget_instances(self):
        # Lazy Instantiation
        if self._widget_instances is None:
            self._widget_instances = []
        return self._widget_instances

    @widget_instances.setter
    def widget_instances(self, value):
        assert isinstance(value, list)
        self._widget_instances = value

    @property
    def widget_connections(self):
        # Lazy Instantiation
        if self._widget_connections is None:
            self._widget_connections = []
        return self._widget_connections

    @widget_connections.setter
    def widget_connections(self, value):
        assert isinstance(value, list)
        self._widget_connections = value

    def __init__(self, path_to_camkes):
        """
        Initialises GraphController
        :param path_to_camkes: string type - path to the .camkes file
        :return: instance of GraphController
        """
        super(GraphController, self).__init__()

        # Initialise properties (not really, just set everything to none and let lazy instantiation any required work)
        # Lazy instantiation is done because subclasses might have different expectation of properties's class
        #   for example root_widget
        self._ast = None
        self._widget_instances = None
        self._widget_connections = None
        self._root_widget = None
        self._component_widget = None
        self._component_dock_widget = None
        # Rest initialised in superclass

        # Model, get a ASTObject from given camkes file
        self.ast = ASTModel.get_ast(path_to_camkes)

        self.setCentralWidget(self.root_widget)
        self.resize(700, 700)

        self.rect = None

        self.sync_model_with_view()

        # self.render()

    def sync_model_with_view(self):

        ast_assembly = self.ast.assembly
        assert isinstance(ast_assembly, Assembly)

        # --- For each instance, create a node in the graph & a widget. ---
        instance_list_copy = list(ast_assembly.instances)

        # Update widget's instance object counterpart
        for widget in self.widget_instances:
            assert isinstance(widget, InstanceWidget)
            new_instance_object = ASTModel.find_instance(instance_list_copy, widget.name)
            if new_instance_object is not None:
                # If found, replace widget's local copy
                self.sync_instance(new_instance_object, widget)
                instance_list_copy.remove(new_instance_object)
            else:
                # Instance object for widget not found, probably deleted, so widget not necessary
                self.root_widget.remove_instance_widget(widget)

        position = 0

        for instance in instance_list_copy:
            # For all new instances (instances without widget counterpart)
            # Make a new widget
            assert isinstance(instance, Instance)

            new_widget = InstanceWidget()
            self.sync_instance(instance, new_widget)
            new_widget.open_component_info.connect(self.show_component_info)

            # Add to internal list of widgets
            self.widget_instances.append(new_widget)

            # TODO: Need to change maybe
            # Add to scene
            self.root_widget.add_instance_widget(new_widget, position + new_widget.preferredSize().width(),
                                                 new_widget.preferredSize().height())
            # self.root_widget.add_instance_widget(new_widget, random.randint(new_widget.preferredSize().width(), 800),
            #                                      random.randint(new_widget.preferredSize().height(), 800))
            position += new_widget.preferredSize().width() + self._connection_length

            print new_widget.pos()

        self.root_widget.clear_connection_widgets()
        self.widget_connections = []

        # Create connection widgets for all connections in assembly
        for connection in self.ast.assembly.connections:

            assert isinstance(connection, Connection)

            for from_instance_end in connection.from_ends:
                assert isinstance(from_instance_end, ConnectionEnd)
                from_instance = from_instance_end.instance
                assert isinstance(from_instance, Instance)

                for to_instance_end in connection.to_ends:
                    assert isinstance(to_instance_end, ConnectionEnd)
                    to_instance = to_instance_end.instance
                    assert isinstance(to_instance, Instance)

                    new_connection_widget = self.create_connection_widget(connection,
                                                                          from_instance.name,
                                                                          from_instance_end.interface.name,
                                                                          to_instance.name,
                                                                          to_instance_end.interface.name)

                    self.widget_connections.append(new_connection_widget)
                    self.root_widget.add_connection_widget(new_connection_widget)

        # Set scene rect to maximum possible size
        max_width = 0
        for widget in self.widget_instances:
            max_width += max(widget.preferredSize().width(), widget.preferredSize().height()) + self._connection_length

        self.root_widget.setViewGeometry(max_width, max_width)

        self.internal_graph_render()

    def create_connection_widget(self, connection, from_instance, from_interface, to_instance, to_interface):
        # Get source and destination widgets
        source_widget = self.find_instance_widget(from_instance)
        dest_widget = self.find_instance_widget(to_instance)
        new_connection_widget = ConnectionWidget(name=connection.name,
                                                 con_type=connection.type.name,
                                                 source=source_widget,
                                                 source_type=connection.type.from_type,
                                                 source_inf_name=from_interface,
                                                 dest=dest_widget,
                                                 dest_type=connection.type.to_type,
                                                 dest_inf_name=to_interface)

        new_connection_widget.connection_object = connection # TODO: Take out

        return new_connection_widget

    def sync_instance(self, instance, widget):
        assert isinstance(instance, Instance)
        assert isinstance(widget, InstanceWidget)

        component = instance.type
        assert isinstance(component, Component)

        widget.name = instance.name
        widget.component_type = component.name
        print widget.component_type
        widget.control = component.control
        widget.hardware = component.hardware

        for provide in component.provides:
            assert isinstance(provide, Provides)
            widget.add_provide(provide.name, provide.type.name)

        for use in component.uses:
            assert isinstance(use, Uses)
            widget.add_use(use.name, use.type.name)

        for emit in component.emits:
            assert isinstance(emit, Emits)
            widget.add_emit(emit.name, emit.type)

        for consumes in component.consumes:
            assert isinstance(consumes, Consumes)
            widget.add_consume(consumes.name, consumes.type, consumes.optional) # Optional bool

        for dataport in component.dataports:
            assert isinstance(dataport, Dataport)
            widget.add_dataport(dataport.name, dataport.type, dataport.optional) # Optional bool

        # TODO add attributes, mutex and semaphores

    def create_graph_rep(self):

        graph_viz = AGraph(strict=False, spline="line", directed=True)

        for widget_instance in self.widget_instances:
            assert isinstance(widget_instance, InstanceWidget)

            size = widget_instance.preferredSize()
            assert isinstance(size, QtCore.QSizeF)

            graph_viz.add_node(widget_instance.name, width=size.width()/72.0,
                               height=size.height()/72.0, shape="rect")

        for connection in self.ast.assembly.connections:

            for from_instance_end in connection.from_ends:
                assert isinstance(from_instance_end, ConnectionEnd)
                from_instance = from_instance_end.instance
                assert isinstance(from_instance, Instance)

                for to_instance_end in connection.to_ends:
                    assert isinstance(to_instance_end, ConnectionEnd)
                    to_instance = to_instance_end.instance
                    assert isinstance(to_instance, Instance)

                    # Add edge
                    graph_viz.add_edge(u=from_instance.name, v=to_instance.name)

        graph_viz.layout('dot')
        raw_dot_data = graph_viz.draw(format='dot')
        print raw_dot_data

        dot_data = Pydot.graph_from_dot_data(raw_dot_data)

        return dot_data

    def internal_graph_render(self):

        dot_data = self.create_graph_rep()

        # Get the size of the graph, and make the canvas the same size
        graph_attributes = dot_data.get_graph_defaults()
        print graph_attributes

        for attribute_dict in graph_attributes:
            if attribute_dict['bb'] is not None:
                rectangle = Common.extract_numbers(attribute_dict['bb'])
                size = (rectangle[1][0]-rectangle[0][0],rectangle[1][1]-rectangle[0][1])
                self.root_widget.setViewGeometry(size[0], size[1])
                break

        # For each widget, get position from dot_data and place them on the screen
        for instance_widget in self.widget_instances:
            assert isinstance(instance_widget, InstanceWidget)

            # Get instance's name
            instance_name = instance_widget.name

            # Get the node representing this instance, and get its attributes
            node_list = dot_data.get_node(instance_name)
            assert len(node_list) == 1  # Should only be one node
            assert isinstance(node_list[0], Pydot.Node)
            node_attributes_dict = node_list[0].get_attributes()

            # Extract position of the node
            node_position_list = Common.extract_numbers(node_attributes_dict['pos'])
            assert len(node_position_list) is 1  # Should only be one position
            node_position = node_position_list[0]

            self.root_widget.add_instance_widget(instance_widget, x_pos=node_position[0], y_pos=node_position[1])

        edge_list = dot_data.get_edges()
        for edge in edge_list:
            assert isinstance(edge, Pydot.Edge)

            for connection_object in self.ast.assembly.connections:
                # For each connection
                assert isinstance(connection_object, Connection)

                # if the edge represents this connections' source and destination
                if edge.get_source() in [y.instance.name for y in connection_object.from_ends] and \
                                edge.get_destination() in [y.instance.name for y in connection_object.to_ends]:

                    # Create an widget with the points and the object

                    for connection_widget in self.widget_connections:
                        assert isinstance(connection_widget, ConnectionWidget)
                        if connection_widget.connection_object is connection_object and \
                            connection_widget.source_instance_widget.name == edge.get_source() and \
                            connection_widget.dest_instance_widget.name == edge.get_destination():
                            edge_widget = connection_widget
                            edge_widget.edge = edge

                    break  # Unnecessary to keep searching once found

    def show_component_info(self, component_name):

        self.component_widget.component_object = ASTModel.find_component(self.ast.items, component_name)

    def find_instance_widget(self, name):
        for instance in self.widget_instances:
            assert isinstance(instance, InstanceWidget)
            if instance.name == name:
                return instance

        return None



    # ... Doesn't work :( ...
    # Add following to sync_model_with_view if using below
        # self.rect = self.root_widget.sceneRect()
        # i = 0
        # while i < 5000:
        #     self.graph_render()
        #     QtCore.QTimer.singleShot(1000, self.graph_render)
        #     i+=1
        # self.graph_render()
        #
        # print self.rect
        #
        # self.root_widget.setSceneRect(self.rect)
        # print self.root_widget.sceneRect().bottomRight()

    @staticmethod
    def force_attraction(x, k):
        return (x*x)/k

    @staticmethod
    def force_repulsion(x,k):
        return (k*k)/x

    def graph_render(self):

        scene = QtWidgets.QGraphicsScene()
        scene.sceneRect()

        rect = self.root_widget.sceneRect()
        assert isinstance(rect, QtCore.QRectF)

        area = rect.width() * rect.height()
        k = math.sqrt(area / len(self.widget_instances))

        print "area = " + str(area) + "  k = " + str(k)

        for instance in self.widget_instances:
            assert isinstance(instance, InstanceWidget)
            instance.velocity = QtCore.QPointF(0,0)

            if instance.pinned:
                # Don't want to move it, so skip this instance
                continue

            for neighbour in self.widget_instances:
                assert isinstance(neighbour, QtWidgets.QGraphicsWidget)
                if instance is not neighbour:
                    dist = QtCore.QPointF(instance.x() - neighbour.x(), instance.y() - neighbour.y())
                    absolute_dist = math.sqrt(dist.x()*dist.x() + dist.y()*dist.y())

                    instance.velocity.setX(instance.velocity.x() +
                                           (dist.x()/absolute_dist)*self.force_repulsion(absolute_dist, k))
                    instance.velocity.setY(instance.velocity.y() +
                                           (dist.y()/absolute_dist)*self.force_repulsion(absolute_dist, k))

            print str(instance.name) + " velocity is: " + str(instance.velocity)

        for connection in self.widget_connections:
            assert isinstance(connection, ConnectionWidget)
            dist = QtCore.QPointF(connection.source_instance_widget.x() - connection.dest_instance_widget.x(),
                                  connection.source_instance_widget.y() - connection.dest_instance_widget.y())

            absolute_dist = math.sqrt(dist.x()*dist.x() + dist.y()*dist.y())
            # TODO: #define

            factor = 1

            if absolute_dist < 100:
                factor = -1

            # Adjust source widget velocity
            if not connection.source_instance_widget.pinned:
                if connection.dest_instance_widget.pinned:
                    factor *= 2

                connection.source_instance_widget.velocity.setX(
                    connection.source_instance_widget.velocity.x() -
                    (dist.x()/absolute_dist)*self.force_attraction(absolute_dist, k)*factor
                )

                connection.source_instance_widget.velocity.setY(
                    connection.source_instance_widget.velocity.y() -
                    (dist.y()/absolute_dist)*self.force_attraction(absolute_dist, k)*factor
                )

                if connection.dest_instance_widget.pinned:
                    factor /= 2

            # Adjust destination widget velocity
            if not connection.dest_instance_widget.pinned:

                if connection.source_instance_widget.pinned:
                    factor *= 2

                connection.dest_instance_widget.velocity.setX(
                    connection.dest_instance_widget.velocity.x() +
                    (dist.x()/absolute_dist)*self.force_attraction(absolute_dist, k)*factor
                )

                connection.dest_instance_widget.velocity.setY(
                    connection.dest_instance_widget.velocity.y() +
                    (dist.y()/absolute_dist)*self.force_attraction(absolute_dist, k)*factor
                )

                if connection.source_instance_widget.pinned:
                    factor /= 2

        for instance in self.widget_instances:
            assert isinstance(instance, InstanceWidget)

            if not instance.pinned:
                # TODO: update scene rect if new position is outside scene

                absolute_velocity = math.sqrt(instance.velocity.x()*instance.velocity.x()
                                              + instance.velocity.y()*instance.velocity.y())

                new_x_pos = instance.x() + (instance.velocity.x()/absolute_velocity) * \
                                           (min(absolute_velocity, self._max_velocity_for_widget_animation))
                new_y_pos = instance.y() + (instance.velocity.y()/absolute_velocity) * \
                                           (min(absolute_velocity, self._max_velocity_for_widget_animation))

                new_x_pos = min(rect.width()/2, max(-rect.width()/2 , new_x_pos))
                new_y_pos = min(rect.height()/2, max(-rect.height()/2, new_y_pos))

                print "instance:" + instance.name + " pinned:" + str(instance.pinned) + " oldPos:" + str(instance.pos()) + " newPos:" + str(new_x_pos) + "," + str(new_y_pos)

                if new_x_pos < instance.preferredSize().width():
                    new_x_pos = instance.preferredSize().width()

                if new_y_pos < instance.preferredSize().height():
                    new_y_pos = instance.preferredSize().height()

                print "instance:" + instance.name + " pinned:" + str(instance.pinned) + " oldPos:" + str(instance.pos()) + " newPos:" + str(new_x_pos) + "," + str(new_y_pos)


                self.root_widget.add_instance_widget(instance, new_x_pos, new_y_pos)

                # Update scene rect to fit all instances (not completed, instances are half in)
                assert isinstance(self.rect, QtCore.QRectF)
                if new_x_pos < self.rect.topLeft().x():
                    self.rect.setTopLeft(QtCore.QPointF(new_x_pos, self.rect.topLeft().y()))
                elif new_x_pos > self.rect.bottomRight().x():
                    self.rect.setBottomRight(QtCore.QPointF(new_x_pos, self.rect.bottomRight().y()))

                if new_y_pos < self.rect.topLeft().y():
                    self.rect.setTopLeft(QtCore.QPointF(self.rect.topLeft().x(), new_y_pos))
                elif new_y_pos > self.rect.bottomRight().y():
                    self.rect.setBottomRight(QtCore.QPointF(self.rect.bottomRight().x(), new_y_pos))

        QtCore.QTimer.singleShot(50, self.graph_render)



def main(arguments):
    # new_controller = GraphController('/home/sthasarathan/Documents/camkes-newExample/apps/simple/simple.camkes')
    # new_controller = GraphController('/home/sthasarathan/Documents/camkes-tool/camkes/parser/tests/good/multiple-ends.camkes')
    # HERE
    # provider = Gtk.CssProvider()

    app = QtWidgets.QApplication(arguments)
    new_controller = GraphController("/home/sthasarathan/Documents/camkes-newExample/apps/complex/complex.camkes")

    # scroll_area = QtWidgets.QScrollArea()
    # # scroll_area.setBackgroundRole(QtGui.QPalette.Base)
    #
    # scroll_area.setWidget(new_controller.root_widget)
    # # scroll_area.setWidgetResizable(True)
    # scroll_area.showmain_window = QtWidgets.QMainWindow()
    # main_window = QtWidgets.QMainWindow()
    # main_window.setCentralWidget(new_controller.root_widget)
    # main_window.resize(700,700)
    # main_window.show()

    new_controller.show()

    # instance = new_controller.widget_instances[0].instance_object
    # assert isinstance(instance, Instance)
    # new_component_window = ComponentWindow(instance.type)
    # new_component_window.setWindowFlags(QtCore.Qt.Window)
    # new_component_window.show()

    app.exec_()



if __name__ == '__main__':
    sys.exit(main(sys.argv))

    # Printing Image as png
    # image = QtGui.QImage(5000,5000, QtGui.QImage.Format_ARGB32)
    # image.fill(QtCore.Qt.transparent)
    #
    # painter = QtGui.QPainter(image)
    # painter.setRenderHint(QtGui.QPainter.Antialiasing)
    # self.root_widget.scene().render(painter)
    # image.save("Test.png")
