#!/usr/bin/env python
# -*- coding: utf-8 -*-

import os
import sys

from gi.repository import Gtk
# import gtk as Gtk

from Controller.base_controller import Controller
from Model.AST_creator import ASTCreator
from View.AST_Widget import ASTWidget

# TODO: Add camkes tools to path, or make an init file or something
from camkes.ast.base import ASTObject
from camkes.ast.liftedast import LiftedAST
from camkes.ast.objects import *




class GraphController(Controller):
    # Default root_widget is a DrawingArea
    @property
    def root_widget(self):
        # Lazy Instantiation
        if self._root_widget is None:
            self._root_widget = Gtk.DrawingArea()
        return self._root_widget

    @root_widget.setter
    def root_widget(self, value):
        assert issubclass(value.__class__, Gtk.DrawingArea) or isinstance(value, Gtk.DrawingArea)
        self._root_widget = value

    @property
    def ast(self):
        return self._ast

    @ast.setter
    def ast(self,value):
        assert issubclass(value.__class__, LiftedAST) or isinstance(value, LiftedAST)
        self._ast = value

    '''Initialises GraphController. Takes a string which is a path to the camkes file to graph'''
    def __init__(self, path_to_camkes):
        super(GraphController, self).__init__()

        # Model, get a ASTObject from given camkes file
        ast_creator = ASTCreator()
        self.ast = ast_creator.get_ast(path_to_camkes)

        # Get one instance - for testing.
        instance = self.ast.assembly.instances[0]
        assert isinstance(instance, Instance)



        # GUI
        self.root_widget = Gtk.DrawingArea()
        self.root_widget.add_child(ASTWidget(instance))




def main():
    new_controller = GraphController('/home/sthasarathan/Documents/camkes-newExample/apps/simple/simple.camkes')
    main_window = Gtk.Window()
    main_window.add(new_controller.root_widget)
    main_window.connect("delete-event", Gtk.main_quit)
    main_window.show_all()
    Gtk.main()


if __name__ == '__main__':
    sys.exit(main())
