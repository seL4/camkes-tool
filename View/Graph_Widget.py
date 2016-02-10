#!/usr/bin/env python
# -*- coding: utf-8 -*-

import json, os, math

from PyQt5 import QtWidgets, QtGui, QtCore, QtSvg
# For QtSvg
# install python-pyqt5.qtsvg
# install libqt5svg5-dev

from pygraphviz import *
# NOTES:    pip install pygraphviz --install-option="--include-path=/usr/include/graphviz"
#                                  --install-option="--library-path=/usr/lib/graphviz/"
#           http://stackoverflow.com/questions/32885486/pygraphviz-importerror-undefined-symbol-agundirected
# from graphviz import Graph
import pydotplus

from camkes.ast import *
from Model.AST_Model import ASTModel
from Model import Common

from Connection_Widget import ConnectionWidget, DataportWidget, ProcedureWidget, EventWidget
from Instance_Widget import InstanceWidget
from Save_Option_Dialog import SaveOptionDialog


class GraphWidget(QtWidgets.QGraphicsView):
    @property
    def connection_widgets(self):
        # Lazy instantiation
        if self._connection_widgets is None:
            self._connection_widgets = []
        return self._connection_widgets

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
    def zoom_in_button(self):
        if self._zoom_in is None:
            self._zoom_in = QtWidgets.QPushButton("Zoom &In", self)
            self._zoom_in.setAutoRepeat(True)
            self._zoom_in.clicked.connect(self.zoom_in)
            self._zoom_in.setShortcut(QtGui.QKeySequence(QtCore.Qt.CTRL + QtCore.Qt.Key_Minus))
            self.update_outer_ui()
        return self._zoom_in

    @property
    def zoom_out_buttom(self):
        if self._zoom_out is None:
            self._zoom_out = QtWidgets.QPushButton("Zoom &Out", self)
            self._zoom_out.setAutoRepeat(True)
            self._zoom_out.clicked.connect(self.zoom_out)
            self._zoom_out.setShortcut(QtGui.QKeySequence(QtCore.Qt.CTRL + QtCore.Qt.Key_Equal))
            self.update_outer_ui()
        return self._zoom_out

    @property
    def save_picture_button(self):
        if self._save_picture_button is None:
            self._save_picture_button = QtWidgets.QPushButton("Save Image", self)
            self._save_picture_button.setAutoRepeat(False)
            self._save_picture_button.clicked.connect(self.save_picture)
            self._save_picture_button.setToolTip("Save the image as a PNG or SVG")
            self.update_outer_ui()
        return self._save_picture_button

    @property
    def autolayout_button(self):
        if self._autolayout_button is None:
            self._autolayout_button = QtWidgets.QPushButton("Auto&layout", self)
            self._autolayout_button.setAutoRepeat(False)
            self._autolayout_button.clicked.connect(self.autolayout)
            self._autolayout_button.setShortcut(QtGui.QKeySequence(QtCore.Qt.CTRL + QtCore.Qt.Key_L))
            self._autolayout_button.setToolTip("Reposition instances using graphviz calculations")
            self.update_outer_ui()
        return self._autolayout_button

    @property
    def ast(self):
        return self._ast

    @ast.setter
    def ast(self, value):
        assert isinstance(value, LiftedAST)
        self._ast = value

        self.sync_model()

        # TODO:
        # If layout exist:
        # Place nodes in original positions. New nodes are placed in middle
        if os.path.isfile(self.get_root_location() + ".layout"):
            self.layout_from_file()
        else:
            # If layout doesn't exist:
            # Use graphviz to place nodes in position
            self.autolayout()

    def random_color_generator(self):
        if self._color_seed is None:
            self._color_seed = 0.9214

        color = QtGui.QColor()
        color = color.fromHslF(self._color_seed, 1, 0.78, 1)

        self._color_seed = (self._color_seed + 0.618033988749895) % 1

        return color

    @property
    def export_action(self):
        if self._export_action is None:
            self._export_action = QtWidgets.QAction("Export as Image", self)
            self._export_action.setShortcut(QtGui.QKeySequence("Ctrl+E"))
            self._export_action.setStatusTip("Save the graph as a PNG or SVG file")
            self._export_action.setToolTip("Save the graph as a PNG or SVG file")
            self._export_action.triggered.connect(self.save_picture)
        return self._export_action


    def __init__(self):
        super(GraphWidget, self).__init__()
        self._connection_widgets = None
        self._widget_instances = None
        self._zoom_in = None
        self._zoom_out = None
        self._save_picture_button = None
        self._export_action = None
        self._autolayout_button = None
        self._ast = None
        self._color_seed = None

        # Place new scene
        scene = QtWidgets.QGraphicsScene(self)
        scene.setItemIndexMethod(QtWidgets.QGraphicsScene.NoIndex)  # TODO: Not sure if this is necessary
        scene.setSceneRect(0, 0, 50, 50)  # Random size, should be given when controller renders
        self.setScene(scene)

        self.setMinimumSize(500, 500)

        self.update_outer_ui()

    # --- Model Functions ---

    def sync_model(self):

        # Get assembly from the ast
        ast_assembly = self.ast.assembly
        assert isinstance(ast_assembly, Assembly)

        # --- For each instance, create a node in the graph & a widget. ---
        instance_list_copy = list(ast_assembly.instances)

        widgets_to_remove = []

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
                widgets_to_remove.append(widget)

        # Delete the widget (since it is not possible to delete the widget during iteration
        for widget in widgets_to_remove:
            self.remove_instance_widget(widget)

        for instance in instance_list_copy:
            # For all new instances (instances without widget counterpart)
            # Make a new widget
            assert isinstance(instance, Instance)

            new_widget = InstanceWidget()
            new_widget.color = self.random_color_generator()
            self.sync_instance(instance, new_widget)
            new_widget.widget_moved.connect(self.update_view)

            # Add to internal list of widgets
            self.widget_instances.append(new_widget)

            # Add to scene
            self.add_instance_widget(new_widget, 0, 0)

        self.clear_connection_widgets()

        # Create connection widgets for all connections in assembly
        assert isinstance(self.ast.assembly, Assembly)
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

                    self.connection_widgets.append(new_connection_widget)
                    self.add_connection_widget(new_connection_widget)

    @staticmethod
    def sync_instance(instance, widget):
        assert isinstance(instance, Instance)
        assert isinstance(widget, InstanceWidget)

        component = instance.type
        assert isinstance(component, Component)

        widget.name = instance.name
        widget.component_type = component.name

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
            widget.add_consume(consumes.name, consumes.type, consumes.optional)  # Optional bool

        for dataport in component.dataports:
            assert isinstance(dataport, Dataport)
            widget.add_dataport(dataport.name, dataport.type, dataport.optional)  # Optional bool

            # TODO add attributes, mutex and semaphores

    def create_connection_widget(self, connection, from_instance, from_interface, to_instance, to_interface):
        # Get source and destination widgets
        source_widget = self.find_instance_widget(from_instance)
        assert source_widget is not None

        dest_widget = self.find_instance_widget(to_instance)
        assert dest_widget is not None

        # Create appropriate connection widget (based on type)
        if connection.type.from_type == Common.Dataport:
            new_connection_widget = DataportWidget(name=connection.name,
                                                   con_type=connection.type.name,
                                                   source=source_widget,
                                                   source_type=connection.type.from_type,
                                                   source_inf_name=from_interface,
                                                   dest=dest_widget,
                                                   dest_type=connection.type.to_type,
                                                   dest_inf_name=to_interface)
        elif connection.type.from_type == Common.Procedure:
            new_connection_widget = ProcedureWidget(name=connection.name,
                                                    con_type=connection.type.name,
                                                    source=source_widget,
                                                    source_type=connection.type.from_type,
                                                    source_inf_name=from_interface,
                                                    dest=dest_widget,
                                                    dest_type=connection.type.to_type,
                                                    dest_inf_name=to_interface)
        elif connection.type.from_type == Common.Event:
            new_connection_widget = EventWidget(name=connection.name,
                                                con_type=connection.type.name,
                                                source=source_widget,
                                                source_type=connection.type.from_type,
                                                source_inf_name=from_interface,
                                                dest=dest_widget,
                                                dest_type=connection.type.to_type,
                                                dest_inf_name=to_interface)
        else:
            new_connection_widget = ConnectionWidget(name=connection.name,
                                                     con_type=connection.type.name,
                                                     source=source_widget,
                                                     source_type=connection.type.from_type,
                                                     source_inf_name=from_interface,
                                                     dest=dest_widget,
                                                     dest_type=connection.type.to_type,
                                                     dest_inf_name=to_interface)

        return new_connection_widget

    def find_instance_widget(self, name):
        for instance in self.widget_instances:
            assert isinstance(instance, InstanceWidget)
            if instance.name == name:
                return instance

        return None

    def add_instance_widget(self, new_widget, x_pos, y_pos):

        assert isinstance(new_widget, InstanceWidget)

        if new_widget not in [x for x in self.scene().items()
                              if isinstance(x, InstanceWidget)]:
            # set parent widget of new widget to be self
            self.scene().addItem(new_widget)
            new_widget.setZValue(5)

        new_widget.setPos(x_pos - (new_widget.preferredSize().width() / 2),
                          y_pos - (new_widget.preferredSize().height() / 2))

    def remove_instance_widget(self, old_widget):

        # Remove from vector list
        self.widget_instances.remove(old_widget)

        # Remove from scene
        scene = self.scene()
        assert isinstance(scene, QtWidgets.QGraphicsScene)
        scene.removeItem(old_widget)

    def add_connection_widget(self, new_connection):
        assert isinstance(new_connection, ConnectionWidget)
        self.scene().addItem(new_connection)
        new_connection.setZValue(1)

    def clear_connection_widgets(self):

        scene = self.scene()
        assert isinstance(scene, QtWidgets.QGraphicsScene)

        for connection in self.connection_widgets:
            scene.removeItem(connection)
            connection.delete()

        del self.connection_widgets[:]

    # --- View Function --
    # TODO: Pick better name
    def layout_from_file(self):

        print "Opening file"

        with open(self.get_root_location() + ".layout", 'r') as input:
            json_input = json.load(input)

            for widget in self.widget_instances:
                assert isinstance(widget, InstanceWidget)
                position = json_input.get(widget.name)
                if position is not None:
                    assert isinstance(position, list)
                    self.add_instance_widget(widget, position[0], position[1])
                else:
                    self.add_instance_widget(widget, self.geometry()/2)

        self.update_view()
        self.save_layout_to_file()

    def save_layout_to_file(self):

        print "Saving file"

        node_positions = {}
        for widget in self.widget_instances:
            assert isinstance(widget, InstanceWidget)

            position_array = [widget.pos().x() - (widget.preferredSize().width() / 2),
                              widget.pos().y() - (widget.preferredSize().height() / 2)]

            node_positions[widget.name] = position_array


        file_location = self.get_root_location() + ".layout"

        with open(file_location,'w') as output:
            json.dump(node_positions,output, indent=4)

    def autolayout(self):
        graph_viz = AGraph(strict=False, spline="line", directed=True)

        for widget_instance in self.widget_instances:
            assert isinstance(widget_instance, InstanceWidget)

            size = widget_instance.preferredSize()
            assert isinstance(size, QtCore.QSizeF)

            graph_viz.add_node(widget_instance.name, width=size.width() / 72.0,
                               height=size.height() / 72.0, shape="rect")

        for connection in self.connection_widgets:
            assert isinstance(connection, ConnectionWidget)
            graph_viz.add_edge(u=connection.source_instance_widget.name, v=connection.dest_instance_widget.name)

        graph_viz.layout('dot')
        raw_dot_data = graph_viz.draw(format='dot')
        print raw_dot_data

        dot_data = pydotplus.graph_from_dot_data(raw_dot_data)

        # Get graphviz height
        graph_attributes = dot_data.get_graph_defaults()

        height = 0

        for attribute_dict in graph_attributes:
            if not isinstance(attribute_dict, dict):
                continue

            if attribute_dict['bb'] is not None:
                rectange = Common.extract_numbers(attribute_dict['bb'])
                height = rectange[1][1]-rectange[0][1]

        for instance_widget in self.widget_instances:
            assert isinstance(instance_widget, InstanceWidget)

            # Get instance's name
            instance_name = instance_widget.name

            # Get the node representing this instance, and get its attributes
            node_list = dot_data.get_node(instance_name)
            assert len(node_list) == 1  # Should only be one node
            assert isinstance(node_list[0], pydotplus.Node)
            node_attributes_dict = node_list[0].get_attributes()

            # Extract position of the node
            node_position_list = Common.extract_numbers(node_attributes_dict['pos'])
            assert len(node_position_list) is 1  # Should only be one position
            node_position = node_position_list[0]

            self.add_instance_widget(instance_widget, x_pos=node_position[0], y_pos=math.fabs(height-node_position[1]))

        self.update_view()
        self.save_layout_to_file()

    def update_view(self):

        rect = self.sceneRect()
        assert isinstance(rect, QtCore.QRectF)

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

            if largest_x < bottom_corner.x():
                largest_x = bottom_corner.x()

            if largest_y < bottom_corner.y():
                largest_y = bottom_corner.y()

        new_rect = QtCore.QRectF(smallest_x, smallest_y, largest_x - smallest_x, largest_y - smallest_y)

        self.setSceneRect(new_rect)

    def update_outer_ui(self):
        bottom_corner = self.geometry().bottomRight()

        zoom_in_position = bottom_corner - QtCore.QPoint(self.zoom_in_button.sizeHint().width(),
                                                         self.zoom_in_button.sizeHint().height()) \
                                         - QtCore.QPoint(20, 40) # 40 due to some weird behaviour with File Menus

        self.zoom_in_button.move(zoom_in_position)
        self.zoom_in_button.show()

        zoom_out_position = zoom_in_position - QtCore.QPoint(self.zoom_out_buttom.sizeHint().width() + 20, 0)

        self.zoom_out_buttom.move(zoom_out_position)
        self.zoom_out_buttom.show()

        save_picture_position = zoom_in_position - QtCore.QPoint(self.save_picture_button.sizeHint().width() -
                                                                 self.zoom_in_button.sizeHint().width(),
                                                                 self.zoom_out_buttom.sizeHint().height() + 20)

        self.save_picture_button.move(save_picture_position)
        self.save_picture_button.show()

        autolayout_position = save_picture_position - QtCore.QPoint(self.autolayout_button.sizeHint().width() -
                                                                 self.save_picture_button.sizeHint().width(),
                                                                 self.save_picture_button.sizeHint().height() + 20)

        self.autolayout_button.move(autolayout_position)
        self.autolayout_button.show()

    def zoom_in(self):
        print "Zoom in"
        self.scale(1.1, 1.1)

    def zoom_out(self):
        print "Zoom out"
        self.scale(0.9, 0.9)

    def save_picture(self):
        print "saving picture"

        if self.ast is None:
            return


        # Ask user whether they want png or svg
        # If png, ask what dimensions
        save_option_dialog = SaveOptionDialog(self, self.sceneRect())
        assert isinstance(save_option_dialog, SaveOptionDialog)
        dialog_code = save_option_dialog.exec_()

        if not dialog_code:
            return

        file_filter = ""

        if save_option_dialog.picture_type() == save_option_dialog.PNG:
            file_filter = "Image (*.png)"
        elif save_option_dialog.picture_type() == save_option_dialog.SVG:
            file_filter = "Scalable Vector Graphics (*.svg)"

        filename = QtWidgets.QFileDialog.getSaveFileName(caption="Save file",
                                                         directory=self.get_root_location(with_name=True),
                                                         filter=file_filter,
                                                         options=QtWidgets.QFileDialog.DontUseNativeDialog)

        image_location = filename[0]  # getSaveFileName returns a tuple. First index of tuple is the file name

        if image_location.rfind('.') != -1:
            image_location = image_location[:image_location.rfind('.')]

        if len(image_location) <= 0:
            # Image location is not valid
            return

        rect = self.sceneRect()
        rect.adjust(-50, -50, 50, 50)

        painter = QtGui.QPainter()

        if save_option_dialog.picture_type() == save_option_dialog.PNG:
            image = QtGui.QImage(save_option_dialog.user_width(),
                                 save_option_dialog.user_height(),
                                 QtGui.QImage.Format_ARGB32)
            image.fill(QtCore.Qt.transparent)

            painter.begin(image)
            painter.setRenderHint(QtGui.QPainter.Antialiasing)
            self.scene().render(painter, source=rect)
            painter.end()

            print image_location
            image.save(image_location + ".png")

        elif save_option_dialog.picture_type() == save_option_dialog.SVG:
            print image_location
            print QtCore.QSize(rect.width(), rect.height())
            print rect
            generator = QtSvg.QSvgGenerator()
            generator.setFileName(image_location + ".svg")
            generator.setSize(QtCore.QSize(rect.width(), rect.height()))
            # generator.setViewBox(rect)
            generator.setTitle(save_option_dialog.user_title())
            generator.setDescription(save_option_dialog.user_description())

            painter.begin(generator)
            painter.setRenderHint(QtGui.QPainter.Antialiasing)
            self.scene().render(painter, source=rect)
            painter.end()

        else:
            return

    def get_root_location(self, with_name=False):
        assembly = self.ast.assembly
        assert isinstance(assembly, Assembly)
        location = assembly.location
        assert isinstance(location, SourceLocation)

        if with_name:
            return location.filename[:location.filename.rfind('.')]
        else:
            find_slash = location.filename.rfind('/')
            if find_slash == -1:
                find_slash = location.filename.rfind('\\') # For windows
            return location.filename[:find_slash+1]

    # --- Overridden Functions ---

    def mousePressEvent(self, mouse_event):
        super(GraphWidget, self).mousePressEvent(mouse_event)

        assert isinstance(mouse_event, QtGui.QMouseEvent)
        print "graph widget - clicked at: " + str(self.mapToScene(mouse_event.pos()))

    def resizeEvent(self, resize_event):
        assert isinstance(resize_event, QtGui.QResizeEvent)
        super(GraphWidget, self).resizeEvent(resize_event)

        self.update_outer_ui()

    def mouseReleaseEvent(self, mouse_event):
        super(GraphWidget, self).mouseReleaseEvent(mouse_event)

        if self.ast:
            self.save_layout_to_file()
