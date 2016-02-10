#!/usr/bin/env python
# -*- coding: utf-8 -*-

import six

from PyQt5 import QtWidgets, QtGui


from Model.AST_Model import ASTModel

from View.Graph_Widget import GraphWidget
from View.Component_Window import ComponentWindow


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
        if self._component_widget is None:
            self._component_widget = ComponentWindow(None)
            self._component_dock_widget = QtWidgets.QDockWidget("Component Info")
            self._component_dock_widget.setWidget(self._component_widget)
            # self.addDockWidget(QtCore.Qt.NoDockWidgetArea, self._component_dock_widget)
        # self._component_dock_widget.setVisible(True)
        return self._component_widget

    # -- Actions --
    @property
    def open_action(self):
        if self._open_action is None:
            self._open_action = QtWidgets.QAction("Open", self)
            self._open_action.setShortcut(QtGui.QKeySequence.Open)
            self._open_action.setStatusTip("Open a new CAmkES ADL file (Top Level only)")
            self._open_action.setToolTip("Open a new CAmkES ADL file (Top Level only)")
            self._open_action.triggered.connect(self.openNewFile)
        return self._open_action
    
    @property
    def quit_action(self):
        if self._quit_action is None:
            self._quit_action = QtWidgets.QAction("Quit", self)
            self._quit_action.setShortcut(QtGui.QKeySequence.Quit)
            self._open_action.setStatusTip("Quit Application")
            self._open_action.setToolTip("Quit Application")
            self._open_action.triggered.connect(self.quit())
        return self._open_action

    def __init__(self, path_to_camkes=None):
        """
        Initialises GraphController
        :param path_to_camkes: string type - path to the .camkes file
        :return: instance of GraphController
        """
        super(GraphController, self).__init__()

        # Initialise properties (not really, just set everything to none and let lazy instantiation any required work)
        # Lazy instantiation is done because subclasses might have different expectation of properties's class for
        #      example root_widget
        self._ast = None
        self._widget_instances = None
        self._widget_connections = None
        self._root_widget = None
        self._component_widget = None
        self._component_dock_widget = None
        self._open_action = None

        self.setWindowTitle("CAmkES Visualisation Tool")

        # Menu
        fileMenu = self.menuBar().addMenu("&File")
        fileMenu.addAction(self.open_action)
        fileMenu.addAction(self.root_widget.export_action)

        # Model, get a ASTObject from given camkes file

        if path_to_camkes is not None:
            self.open_ast(path_to_camkes)

        self.setCentralWidget(self.root_widget)
        self.resize(700, 700)

        self.rect = None

    def openNewFile(self):
        new_file = QtWidgets.QFileDialog.getOpenFileName(caption="Open CAmkES ADL file",
                                                         filter="CAmkES ADL (*.camkes)",
                                                         options=QtWidgets.QFileDialog.DontUseNativeDialog)
        self.open_ast(new_file[0])

    def open_ast(self, path_to_file):

        assert isinstance(path_to_file, six.string_types)

        if len(path_to_file) > 1:
            self.root_widget.ast = ASTModel.get_ast(path_to_file)

            # find last / (or last \ in windows)
            start_of_filename = path_to_file.rfind("/")
            if start_of_filename == -1:
                start_of_filename = path_to_file.rfind('\\')

            if start_of_filename == -1:
                start_of_filename = 0
            else:
                start_of_filename += 1

            self.setWindowTitle(path_to_file[start_of_filename:path_to_file.rfind('.')])

    def quit(self):
        if self.root_widget.ast:
            self.root_widget.save_layout_to_file()

        QtWidget.QApplication.quit()

    def show_component_info(self, component_name):

        self.component_widget.component_object = ASTModel.find_component(self.ast.items, component_name)
