#!/usr/bin/env python
# -*- coding: utf-8 -*-

import sys, os

# sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../../'))
# sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '../'))

from PyQt5 import QtWidgets


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

    def __init__(self, path_to_camkes):
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

        # Model, get a ASTObject from given camkes file
        self.root_widget.ast = ASTModel.get_ast(path_to_camkes)

        self.setCentralWidget(self.root_widget)
        self.resize(700, 700)

        self.rect = None

    def show_component_info(self, component_name):

        self.component_widget.component_object = ASTModel.find_component(self.ast.items, component_name)


def main(arguments):

    app = QtWidgets.QApplication(arguments)
    # new_controller = GraphController("/home/sthasarathan/Documents/camkes-newExample/apps/complex/complex.camkes")
    new_controller = GraphController("/home/sthasarathan/Documents/camkes-newExample/apps/coffeeSimple/coffeeDD.camkes")

    # new_controller = GraphController("/home/sthasarathan/Documents/CAMKES-APPS/camkes-kitty-HDDMA/apps/bilbyfs/bilbyfs.camkes")
    # new_controller = GraphController("/home/sthasarathan/Documents/test/cddc/apps/cddc/cddc.camkes")
    # new_controller = GraphController("/home/sthasarathan/Documents/quadcopter/quadcopter-next/apps/quadcopter/quadcopter.camkes")

    new_controller.show()

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
