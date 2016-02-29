#!/usr/bin/env python
# -*- coding: utf-8 -*-

import six

from PyQt5 import QtWidgets, QtGui

# Required for converting ANSI Red color messages to HTML for QMessageBox
from ansi2html import Ansi2HTMLConverter

# CAmkES Exception handler
from camkes.internal.exception import CAmkESError

# Model and View imports
from Model.AST_Model import ASTModel

from View.Graph_Widget import GraphWidget
from View.Component_Window import ComponentWindow


class GraphController(QtWidgets.QMainWindow):

    # --- PROPERTIES ---

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

    # Attempt at creating a window which pops up when a user clickes on a component. Doesn't work atm
    # @property
    # def component_widget(self):
    #     if self._component_widget is None:
    #         self._component_widget = ComponentWindow(None)
    #         self._component_dock_widget = QtWidgets.QDockWidget("Component Info")
    #         self._component_dock_widget.setWidget(self._component_widget)
    #         # self.addDockWidget(QtCore.Qt.NoDockWidgetArea, self._component_dock_widget)
    #     # self._component_dock_widget.setVisible(True)
    #     return self._component_widget

    # -- Actions --
    @property
    def open_action(self):
        '''
        :return: QAction for opening files
        '''
        if self._open_action is None:
            self._open_action = QtWidgets.QAction("Open", self)
            self._open_action.setShortcut(QtGui.QKeySequence.Open)
            self._open_action.setStatusTip("Open a new CAmkES ADL file (Top Level only)")
            self._open_action.setToolTip("Open a new CAmkES ADL file (Top Level only)")
            self._open_action.triggered.connect(self.open_new_file)
        return self._open_action
    
    @property
    def quit_action(self):
        '''
        :return: QAction for closing the application
        '''
        if self._quit_action is None:
            self._quit_action = QtWidgets.QAction("Quit", self)
            self._quit_action.setShortcut(QtGui.QKeySequence.Quit)
            self._quit_action.setStatusTip("Quit Application")
            self._quit_action.setToolTip("Quit Application")
            self._quit_action.triggered.connect(self.quit)
        return self._quit_action

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
        self._component_widget = None
        self._component_dock_widget = None
        self._open_action = None
        self._quit_action = None

        self.setWindowTitle("CAmkES Visualisation Tool")

        # Menu
        fileMenu = self.menuBar().addMenu("&File")
        fileMenu.addAction(self.open_action)
        fileMenu.addAction(self.root_widget.export_action)

        fileMenu.addSeparator()
 
        fileMenu.addAction(self.quit_action)

        viewMenu = self.menuBar().addMenu("&View")
        viewMenu.addAction(self.root_widget.show_components_action)


        # Get a ASTObject from given camkes file
        if path_to_camkes is not None:
            self.open_ast(path_to_camkes)

        self.setCentralWidget(self.root_widget)
        self.resize(700, 700)

        self.rect = None

    # --- FUNCTION CALLS ---

    def show_component_info(self, component_name):
        '''
        Open a window (or dock window) with information about component type
        :param component_name: The component type of an instance
        :return
        '''
        self.component_widget.component_object = ASTModel.find_component(self.ast.items, component_name)

    def open_ast(self, path_to_file):
        '''
        Opens the given camkes file. Deals with the drawing. Shows an error if a CAmkES Error occurs
        :param path_to_file: The path to the camkes file. A string such as "/home/bob/camkes/app/kitty/kitty.camkes
        :return
        '''

        assert isinstance(path_to_file, six.string_types)

        # Checks to see if path is not empty
        if len(path_to_file) > 1:
            try:
                # Set the AST of GraphWidget
                self.root_widget.ast = ASTModel.get_ast(path_to_file)
            except CAmkESError as error:
                # If error occurred

                # For terminal users:
                print str(error)

                # Show Error as a message popup
                messageBox = QtWidgets.QMessageBox()
                messageBox.setText("Syntax Error")

                # Convert all ANSI codes to HTML
                conv = Ansi2HTMLConverter(inline=True, dark_bg=False)
                html = conv.convert(str(error), full=False)
                html = html.replace('\n', '<br/>').replace('^','')
                messageBox.setInformativeText('<p style="font-family: monospace;">' + html + '</p>')
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
        '''
        Action for opening new file. Opens a dialog and gets the path to the .camkes file
        :return:
        '''
        new_file = QtWidgets.QFileDialog.getOpenFileName(caption="Open CAmkES ADL file",
                                                         filter="CAmkES ADL (*.camkes)")
        self.open_ast(new_file[0])

    def quit(self):
        '''
        Action for quiting the program. Saves the final layout and closes.
        :return:
        '''
        if self.root_widget.ast:
            self.root_widget.save_layout_to_file()

        QtWidgets.QApplication.quit()

