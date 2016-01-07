#!/usr/bin/env python
# -*- coding: utf-8 -*-

import sys

# TODO: should be able to remove this, as controller shouldn't be dependent on graphics library (that's the goal)
from PyQt5 import QtWidgets, QtGui, QtCore

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
from Model.AST_creator import ASTCreator
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
        print "accessing component_widget"
        if self._component_widget is None:
            self._component_widget = ComponentWindow(None)
            self._component_dock_widget = QtWidgets.QDockWidget("Component Info")
            self._component_dock_widget.setWidget(self._component_widget)
            self.addDockWidget(QtCore.Qt.RightDockWidgetArea, self._component_dock_widget)
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
        # Rest initialised in superclass

        # Model, get a ASTObject from given camkes file
        self.ast = ASTCreator.get_ast(path_to_camkes)

        self.setCentralWidget(self.root_widget)
        self.resize(700,700)

        self.sync_model_with_view()

        # self.render()

    def sync_model_with_view(self):

        ast_assembly = self.ast.assembly
        assert isinstance(ast_assembly, Assembly)

        # Clear arrays of instances and connections
        self.widget_instances = []
        self.widget_connections = []

        # For each instance, create a node in the graph & a widget.
        for instance in ast_assembly.instances:
            assert isinstance(instance, Instance)

            new_widget = InstanceWidget(instance)
            new_widget.openComponentInfo.connect(self.show_component_info)

            self.widget_instances.append(new_widget)

        self.render()

    def create_graph_rep(self):

        graph_viz = AGraph(strict=False, spline="line", directed=True)

        for widget_instance in self.widget_instances:
            assert isinstance(widget_instance, InstanceWidget)

            instance = widget_instance.instance_object
            assert isinstance(instance, Instance)

            size = widget_instance.sizeHint()
            assert isinstance(size, QtCore.QSize)

            graph_viz.add_node(instance.name, width=size.width()/72.0,
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

    def render(self):

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
            instance_name = instance_widget.instance_name

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

                    edge_widget = ConnectionWidget(connection_object, edge)
                    self.widget_connections.append(edge_widget)
                    self.root_widget.add_connection_widget(edge_widget)

                    break  # Unnecessary to keep searching once found

    def show_component_info(self, mouse_event, instance):
        print "clicked " + str(instance.name)
        self.component_widget.set_component_object(instance.type, mouse_event)




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
