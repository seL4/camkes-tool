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

# TODO: use pydotplus properly
import pydotplus as Pydot


from Controller.base_controller import Controller
from Model.AST_creator import ASTCreator
from View.AST_Widget import ASTWidget
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

        # Create graph
        graph_viz = AGraph(strict=False)  # TODO: Consider renaming (easy to do with refactor :)

        # For each instance, create a node in the graph & TODO: create a widget
        for instance in ast_assembly.instances:
            assert isinstance(instance, Instance)

            # Add widget TODO: Not final
            new_widget_builder = Gtk.Builder()
            new_widget_builder.add_from_file("../View/gladeASTTest.builder")

            instance_label = new_widget_builder.get_object("instance_name_label")
            assert isinstance(instance_label, Gtk.Label)
            instance_label.set_text(instance.name)

            component_type_label = new_widget_builder.get_object("component_type")
            assert isinstance(component_type_label, Gtk.Label)
            component_type_label.set_text(instance.type.name)

            # new_widget = new_widget_builder.get_object("Instance_frame")

            # TODO: Is the following necessary?, should it be checking Gtk.Widget instead
            # assert isinstance(new_widget, Gtk.Frame)

            # TODO: Better type to add to widget_instance list (separate view class?)
            self.widget_instances.append(new_widget_builder)

            # Add node
            graph_viz.add_node(instance.name)

        # For all connections, create an edge & TODO: creates a widget
        for connection in ast_assembly.connections:
            assert isinstance(connection, Connection)

            # TODO: Only works for one end per connection
            from_instance = connection.from_end.instance
            assert isinstance(from_instance, Instance)
            to_instance = connection.to_end.instance
            assert isinstance(to_instance, Instance)

            # Add edge
            graph_viz.add_edge(u=from_instance.name, v=to_instance.name)

        # Generate the graph (add positions to each node and edges)
        graph_viz.layout('dot')
        raw_dot_data = graph_viz.draw(format='dot')
        print raw_dot_data

        dot_data = Pydot.graph_from_dot_data(raw_dot_data)
        assert isinstance(dot_data, Pydot.Dot)

        # Create base GUI
        self.root_widget = Gtk.Layout()

        # For each widget, get position from dot_data and place them on the screen
        for widget_builder in self.widget_instances:
            assert isinstance(widget_builder, Gtk.Builder)
            instance_name = widget_builder.get_object("instance_name_label").get_text()
            node_list= dot_data.get_node(instance_name)
            assert len(node_list) == 1
            assert isinstance(node_list[0], Pydot.Node)
            node_attributes_dict = node_list[0].get_attributes()

            node_position = re.findall("[-+]?\d+[.]?\d*", node_attributes_dict['pos'])
            x_pos = float(node_position[0])
            y_pos = float(node_position[1])

            self.root_widget.put(widget_builder.get_object("Instance_frame"), x_pos, y_pos)





def main():
    #new_controller = GraphController('/home/sthasarathan/Documents/camkes-newExample/apps/simple/simple.camkes')
    new_controller = GraphController('/home/sthasarathan/Documents/camkes-newExample/apps/uart/uart.camkes')
    main_window = Gtk.Window()
    # main_window.set_size_request(1000,1000)
    main_window.add(new_controller.root_widget)
    main_window.connect("delete-event", Gtk.main_quit)
    main_window.show_all()
    Gtk.main()


if __name__ == '__main__':
    sys.exit(main())
