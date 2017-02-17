#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2017, Data61
# Commonwealth Scientific and Industrial Research Organisation (CSIRO)
# ABN 41 687 119 230.
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(DATA61_BSD)

import six

from PyQt5 import QtWidgets, QtGui, QtCore

# Required for converting ANSI Red color messages to HTML for QMessageBox
from ansi2html import Ansi2HTMLConverter

# CAmkES Exception handler
from camkes.internal.exception import CAmkESError

# Model and View imports
from Model.AST_Model import ASTModel

from View.Graph_Widget import GraphWidget

class GraphController(QtWidgets.QMainWindow):

    # --- PROPERTIES ---

    # Hidden import path array
    __import_paths = []

    # Default root_widget is a GraphWidget
    @property
    def root_widget(self):
        # Lazy Instantiation
        if self._root_widget is None:
            self._root_widget = GraphWidget(self.property_dock_widget)
        return self._root_widget

    @root_widget.setter
    def root_widget(self, value):
        assert isinstance(value, GraphWidget)
        self._root_widget = value

    # -- Actions --
    @property
    def open_action(self):
        """
        :return: QAction for opening files
        """
        if self._open_action is None:
            self._open_action = QtWidgets.QAction("Open", self)
            self._open_action.setShortcut(QtGui.QKeySequence.Open)
            self._open_action.setStatusTip("Open a new CAmkES ADL file (Top Level only)")
            self._open_action.setToolTip("Open a new CAmkES ADL file (Top Level only)")
            self._open_action.triggered.connect(self.open_new_file)
        return self._open_action
    
    @property
    def quit_action(self):
        """
        :return: QAction for closing the application
        """

        if self._quit_action is None:
            self._quit_action = QtWidgets.QAction("Quit", self)
            self._quit_action.setShortcut(QtGui.QKeySequence.Quit)
            self._quit_action.setStatusTip("Quit Application")
            self._quit_action.setToolTip("Quit Application")
            self._quit_action.triggered.connect(self.quit)
        return self._quit_action

    @property
    def import_path_action(self):
        """
        :return: QAction for opening files
        """
        if self._import_path_action is None:
            self._import_path_action = QtWidgets.QAction("Add Import Paths", self)
            self._import_path_action.setShortcut(QtGui.QKeySequence.Italic)  # Gives us Ctrl+I (or Cmd+I)
            self._import_path_action.setStatusTip("Open a new CAmkES ADL file (Top Level only)")
            self._import_path_action.setToolTip("Open a new CAmkES ADL file (Top Level only)")
            self._import_path_action.triggered.connect(self.add_import_path)
        return self._import_path_action

    @property
    def property_dock_widget(self):
        """
        :return: The dock widget for properties
        """
        if self._property_dock is None:
            self._property_dock = QtWidgets.QDockWidget("Properties", self)
            self._property_dock.setAllowedAreas(QtCore.Qt.LeftDockWidgetArea |
                                                QtCore.Qt.RightDockWidgetArea)
        return self._property_dock

    def __init__(self, path_to_camkes=None):
        """
        Initialises GraphController
        :param path_to_camkes: string type - path to the .camkes file
        :return: instance of GraphController
        """
        super(GraphController, self).__init__()

        # Initialise properties (not really, just set everything to none and let lazy instantiation any required work)
        # Lazy instantiation is done because subclasses might have different expectation of properties's class.
        self._ast = None
        self._widget_instances = None
        self._widget_connections = None
        self._root_widget = None
        self._open_action = None
        self._quit_action = None
        self._import_path_action = None
        self._property_dock = None

        self.setWindowTitle("CAmkES Visualisation Tool")

        # Menu
        fileMenu = self.menuBar().addMenu("&File")
        fileMenu.addAction(self.open_action)
        fileMenu.addAction(self.root_widget.export_action)

        fileMenu.addSeparator()
 
        fileMenu.addAction(self.quit_action)

        editMenu = self.menuBar().addMenu("&Edit")
        editMenu.addAction(self.import_path_action)

        viewMenu = self.menuBar().addMenu("&View")
        viewMenu.addAction(self.root_widget.show_components_action)

        # Get a ASTObject from given camkes file
        if path_to_camkes is not None:
            self.open_ast(path_to_camkes)

        self.setCentralWidget(self.root_widget)
        self.resize(700, 900)

        self.rect = None

        self.property_dock_widget.setWidget(QtWidgets.QWidget())
        self.addDockWidget(QtCore.Qt.RightDockWidgetArea, self.property_dock_widget)
        self.setTabPosition(QtCore.Qt.LeftDockWidgetArea | QtCore.Qt.RightDockWidgetArea, QtWidgets.QTabWidget.North)
        self.setTabShape(QtWidgets.QTabWidget.Triangular)

    # --- FUNCTION CALLS ---

    def open_ast(self, path_to_file, import_paths=None):
        """
        Opens the given camkes file. Deals with the drawing. Shows an error if a CAmkES Error occurs
        :param path_to_file: The path to the camkes file. A string such as "/home/bob/camkes/app/kitty/kitty.camkes
        :return
        """

        assert isinstance(path_to_file, six.string_types)

        # Checks to see if path is not empty
        if len(path_to_file) > 1:
            try:
                # Set the AST of GraphWidget
                self.root_widget.ast = ASTModel.get_ast(path_to_file, import_paths)
            except CAmkESError as error:
                # If error occurred

                # For terminal users:
                print "Error occurred when opening the file... please refer to the following error"
                print error

                # Show Error as a message popup
                messageBox = QtWidgets.QMessageBox()
                messageBox.setText("Syntax Error")

                # Convert all ANSI codes to HTML
                conv = Ansi2HTMLConverter(inline=True, dark_bg=False)
                html = conv.convert(str(error), full=False)
                html = html.replace('\n', '<br/>').replace('^','')
                messageBox.setInformativeText('<p style="font-family: monospace;"> %s </p>' % html)
                messageBox.exec_()
            else:
                # If no error, AST would have been successfully set. Change Window Title to name of file.

                # find last / (or last \ in windows)
                start_of_filename = path_to_file.rfind("/")
                if start_of_filename == -1:
                    # Might be a windows machine
                    start_of_filename = path_to_file.rfind('\\')

                if start_of_filename == -1:
                    # If still not found, assume its just the name of the file.
                    start_of_filename = 0
                else:
                    start_of_filename += 1

                self.setWindowTitle(path_to_file[start_of_filename:path_to_file.rfind('.')])

    # --- EVENTS ---

    def open_new_file(self):
        """
        Action for opening new file. Opens a dialog and gets the path to the .camkes file
        :return:
        """

        new_file = QtWidgets.QFileDialog.getOpenFileName(caption="Open CAmkES ADL file",
                                                         filter="CAmkES ADL (*.camkes)")
        self.open_ast(new_file[0], self.__import_paths)

    def quit(self):
        """
        Action for quiting the program. Saves the final layout and closes.
        :return:
        """

        if self.root_widget.ast:
            self.root_widget.save_layout_to_file()

        QtWidgets.QApplication.quit()

    def add_import_path(self):
        """
        Prompts the user to insert one or many import paths, to be placed as an argument to the parser
        when opening a top level camkes file
        """

        user_input = QtWidgets.QInputDialog.getText(None, "Add Import Paths.",
                                                    "Add Import Paths. If you have many, separate with spaces.")

        user_import_paths = user_input[0].split()
        if user_import_paths.count != 0:
            self.__import_paths.extend(user_import_paths)

        print "Import Paths are: " + str(self.__import_paths)

