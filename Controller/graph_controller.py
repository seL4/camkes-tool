#!/usr/bin/env python
# -*- coding: utf-8 -*-

import os
import sys
import re

from gi.repository import Gtk  # For graphics
# import gtk as Gtk
from pygraphviz import *
# NOTES:    pip install pygraphviz --install-option="--include-path=/usr/include/graphviz"
#                                  --install-option="--library-path=/usr/lib/graphviz/"
#           http://stackoverflow.com/questions/32885486/pygraphviz-importerror-undefined-symbol-agundirected
# from graphviz import Graph

# TODO:
# WARNING NEEED TO INSTALLL python-gi-cairo
# sudo apt-get install python-gi-cairo

# TODO: use pydotplus properly
import pydotplus as Pydot


from Controller.base_controller import Controller
from Model.AST_creator import ASTCreator
from View.Connection_Widget import ConnectionWidget
from View.Instance_Widget import InstanceWidget

# TODO: Add camkes tools to path, or make an init file or something
from camkes.ast.base import ASTObject
from camkes.ast.liftedast import LiftedAST
from camkes.ast.objects import *


class GraphController(Controller):
    # Default root_widget is a Gtk.Layout
    @property
    def root_widget(self):
        # Lazy Instantiation
        if self._root_widget is None:
            self._root_widget = Gtk.Layout()
        return self._root_widget

    @root_widget.setter
    def root_widget(self, value):
        assert issubclass(value.__class__, Gtk.Layout) or isinstance(value, Gtk.Layout)
        self._root_widget = value

    @property
    def ast(self):
        return self._ast

    @ast.setter
    def ast(self, value):
        assert issubclass(value.__class__, LiftedAST) or isinstance(value, LiftedAST)
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

    '''Initialises GraphController. Takes a string which is a path to the camkes file to graph'''

    def __init__(self, path_to_camkes):
        super(GraphController, self).__init__()

        # Initialise properties (not really, just set everything to none and let lazy instantiation any required work)
        # Lazy instantiation is done because subclasses might have different expectation of properties's class
        #   for example root_widget
        self._ast = None
        self._widget_instances = None
        self._widget_connections = None
        # Rest initialised in superclass

        # Model, get a ASTObject from given camkes file
        ast_creator = ASTCreator()
        self.ast = ast_creator.get_ast(path_to_camkes)

        ast_assembly = self.ast.assembly
        assert isinstance(ast_assembly, Assembly)

        # For each instance, create a node in the graph & a widget
        for instance in ast_assembly.instances:
            assert isinstance(instance, Instance)

            new_widget = InstanceWidget(instance)

            self.widget_instances.append(new_widget)

        # Create base GUI
        self.root_widget = Gtk.Layout()

        # For each widget, get position from dot_data and place them on the screen
        for instance_widget in self.widget_instances:

            self.root_widget.put(instance_widget, 0, 0)

        self.render()

    def render(self):
        ast_assembly = self.ast.assembly
        # assert isinstance(ast_assembly, Assembly)

        # Create graph
        graph_viz = AGraph(strict=False, spline="line", directed=True)
        # TODO: Consider renaming above (easy to do with refactor :)

        # For each instance, create a node in the graph & a widget
        for widget_instance in self.widget_instances:
            instance = widget_instance.instance_object

            # Add node
            size = widget_instance.get_preferred_size()[-1]

            # graph_viz.add_node(instance.name)
            # Divide by 72 because of points to inches conversion
            graph_viz.add_node(instance.name, width=size.width/72,
                               height=size.height/72, shape="rect")

        # For all connections, create an edge & TODO: creates a widget
        for connection in ast_assembly.connections:
            assert isinstance(connection, Connection)

            for from_instance_end in connection.from_ends:
                assert isinstance(from_instance_end, ConnectionEnd)
                from_instance = from_instance_end.instance

                for to_instance_end in connection.to_ends:
                    assert isinstance(to_instance_end, ConnectionEnd)
                    to_instance = to_instance_end.instance

                    assert isinstance(from_instance, Instance) and isinstance(to_instance, Instance)
                    # Add edge
                    graph_viz.add_edge(u=from_instance.name, v=to_instance.name)

        # Generate the graph (add positions to each node and edges)
        graph_viz.layout('dot')
        raw_dot_data = graph_viz.draw(format='dot')
        print raw_dot_data

        dot_data = Pydot.graph_from_dot_data(raw_dot_data)
        assert isinstance(dot_data, Pydot.Dot)

        # For each widget, get position from dot_data and place them on the screen
        for instance_widget in self.widget_instances:
            assert isinstance(instance_widget, InstanceWidget)

            # Get instance's name
            instance_name = instance_widget.instance_name

            # Get the node representing this instance, and get its attributes
            node_list= dot_data.get_node(instance_name)
            assert len(node_list) == 1              # Should only be one node
            assert isinstance(node_list[0], Pydot.Node)
            node_attributes_dict = node_list[0].get_attributes()

            # Extract position of the node
            node_position_list = self.extract_numbers(re.findall("([-+]?\d+[.]?\d*)[,]([-+]?\d+[.]?\d*)",
                                                                 node_attributes_dict['pos']))
            assert len(node_position_list) is 1     # Should only be one position
            node_position = node_position_list[0]

            self.root_widget.move(instance_widget, node_position[0], node_position[1])

        '''
        # DOESN"T WORK
        # DRAW ARROW

        # get an edge for testing
        edge = dot_data.get_edges()[0]
        assert isinstance(edge, Pydot.Edge)

        # Get the dictionary of attributes for the edge
        edge_attributes_dict = edge.get_attributes()

        # get a list of tuples of all points
        edge_points = self.extract_numbers(re.findall("([-+]?\d+[.]?\d*)[,]([-+]?\d+[.]?\d*)",
                                                      edge_attributes_dict['pos']))

        print "edges " + str(edge_points)

        # edge_widget = ASTWidget(widget_controller=self, points=edge_points)
        edge_widget = ConnectionWidget()
        edge_widget.set_size_request(abs(edge_points[1][0] - edge_points[0][0]),
                                     abs(edge_points[1][1] - edge_points[0][1]))

        self.root_widget.put(edge_widget, edge_points[0][0], edge_points[0][1])
        '''


    # Extra Helper Functions
    @staticmethod
    def extract_numbers(list_of_tuples_stringnumbers):  # TODO: consider renaming list_of_tuples_...
        new_list = list()
        for next_tuple in list_of_tuples_stringnumbers:
            converted_tuple = (float(next_tuple[0]), float(next_tuple[1]))
            new_list.append(converted_tuple)

        return new_list




def main():
    #new_controller = GraphController('/home/sthasarathan/Documents/camkes-newExample/apps/simple/simple.camkes')

    # HERE
    provider = Gtk.CssProvider()

    new_controller = GraphController('/home/sthasarathan/Documents/camkes-tool/camkes/parser/tests/good/multiple-ends.camkes')
    main_window = Gtk.Window()
    main_window.add(new_controller.root_widget)
    main_window.connect("delete-event", Gtk.main_quit)
    main_window.show_all()
    Gtk.main()


if __name__ == '__main__':
    sys.exit(main())
