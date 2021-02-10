#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

import json, os, math

from PyQt5 import QtWidgets, QtGui, QtCore, QtSvg

from graphviz import *
import pydotplus

from camkes.ast import *
from Model.AST_Model import ASTModel
from Model import Common

from Connection_Widget import ConnectionWidget, DataportWidget, ProcedureWidget, EventWidget
from Instance_Widget import InstanceWidget
from Save_Option_Dialog import SaveOptionDialog
from Interface.Property import PropertyInterface

class GraphWidget(QtWidgets.QGraphicsView):
    """
    GraphWidget - Manages the instances and connection widgets within a scene - and keeps it in sync with AST.
    """

    # --- PROPERTIES ---

    @property
    def connection_widgets(self):
        if self._connection_widgets is None:
            self._connection_widgets = []
        return self._connection_widgets

    @property
    def widget_instances(self):
        if self._widget_instances is None:
            self._widget_instances = []
        return self._widget_instances

    @widget_instances.setter
    def widget_instances(self, value):
        assert isinstance(value, list)
        self._widget_instances = value

    @property
    def context_menu(self):
        # Setting up context (right click) menu
        if self._context_menu is None:
            menu = QtWidgets.QMenu()
            proxy_menu = self.scene().addWidget(menu)
            proxy_menu.setFlag(QtWidgets.QGraphicsItem.ItemIgnoresTransformations)
            proxy_menu.setZValue(10)
            self._context_menu = proxy_menu
        return self._context_menu

    @property
    def zoom_in_button(self):
        if self._zoom_in is None:
            self._zoom_in = QtWidgets.QPushButton("Zoom &In", self)
            self._zoom_in.setAutoRepeat(True)
            self._zoom_in.clicked.connect(self.zoom_in)
            self._zoom_in.setShortcut(QtGui.QKeySequence(QtCore.Qt.CTRL + QtCore.Qt.Key_Minus))
            self._zoom_in.setShortcut(QtGui.QKeySequence(QtCore.Qt.CTRL + QtCore.Qt.Key_Equal))
            self.update_outer_ui()
        return self._zoom_in

    @property
    def zoom_out_buttom(self):
        if self._zoom_out is None:
            self._zoom_out = QtWidgets.QPushButton("Zoom &Out", self)
            self._zoom_out.setAutoRepeat(True)
            self._zoom_out.clicked.connect(self.zoom_out)
            self._zoom_out.setShortcut(QtGui.QKeySequence(QtCore.Qt.CTRL + QtCore.Qt.Key_Minus))
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

        # When AST is set, graph is updated.
        self.sync_model()

        # Layout
        if os.path.isfile("%s.visualCAmkES.layout" % self.get_root_location()):
            # If layout exist, place nodes in original positions. New nodes are placed in middle
            self.layout_from_file()
        else:
            # If layout doesn't exist use graphviz to place nodes in position
            self.autolayout()

    # ----- ACTIONS -----
    @property
    def export_action(self):
        if self._export_action is None:
            self._export_action = QtWidgets.QAction("Export as Image", self)
            self._export_action.setShortcut(QtGui.QKeySequence("Ctrl+E"))
            self._export_action.setStatusTip("Save the graph as a PNG or SVG file")
            self._export_action.setToolTip("Save the graph as a PNG or SVG file")
            self._export_action.triggered.connect(self.save_picture)
        return self._export_action

    @property
    def show_components_action(self):
        if self._show_components_action is None:
            self._show_components_action = QtWidgets.QAction("Show all components", self)
            self._show_components_action.setStatusTip("Set all components to not hidden")
            self._show_components_action.setToolTip("Set all components to not hidden")
            self._show_components_action.triggered.connect(self.show_all_components)
        return self._show_components_action

    # ---- OTHER WIDGETS ----
    @property
    def property_widget_dock(self):
        return self._property_widget_dock

    # --- INITIALISATION ---

    def __init__(self, property_widget_dock):
        super(GraphWidget, self).__init__()
        self._connection_widgets = None
        self._widget_instances = None
        self._zoom_in = None
        self._zoom_out = None
        self._save_picture_button = None
        self._export_action = None
        self._show_components_action = None
        self._autolayout_button = None
        self._ast = None
        self._color_seed = None
        self._property_widget_dock = property_widget_dock

        self._context_menu = None

        # Create new scene
        scene = QtWidgets.QGraphicsScene(self)
        scene.setItemIndexMethod(QtWidgets.QGraphicsScene.NoIndex)  # TODO: Not sure if this is necessary
        scene.setSceneRect(0, 0, 50, 50)  # Random size, should be given when controller renders
        self.setScene(scene)

        self.setMinimumSize(500, 500)

        # Update button positions
        self.update_outer_ui()

    # --- Model Methods ---

    def sync_model(self):
        """
        Updates view to the model representation
        """

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
                # Instance object for widget not found, probably deleted - so widget not necessary
                widgets_to_remove.append(widget)

        # Delete the widget (since it is not possible to delete the widget during iteration)
        for widget in widgets_to_remove:
            self.remove_instance_widget(widget)

        for instance in instance_list_copy:
            # For all new instances (instances without widget counterpart)
            # Make a new widget
            assert isinstance(instance, Instance)

            new_widget = InstanceWidget(self.context_menu)
            new_widget.color = self.random_color_generator()
            self.sync_instance(instance, new_widget)
            new_widget.widget_moved.connect(self.update_view)

            # Add to internal list of widgets
            self.widget_instances.append(new_widget)

            # Add to scene
            self.reposition_instance_widget(new_widget, 0, 0)

        self.clear_connection_widgets()

        # Create connection widgets for all connections in assembly
        # Instead of syncing connections, ConnectionWidgets are considered disposable. Just delete all and remake them
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

    # -- Instances Methods --

    @staticmethod
    def sync_instance(instance, widget):
        """
        Sync between Instance object and InstanceWidget object
        :param instance: the model camkes.ast.Instance to sync from
        :param widget: the View.InstanceWidget object to be synced to
        """

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

    def reposition_instance_widget(self, new_widget, x_pos, y_pos):
        """
        Add widget (or reposition) to scene.
        :param new_widget: widget to be added (or repositioned)
        :param x_pos: Middle of widget (x value)
        :param y_pos: Middle of widget (y value)
        :return:
        """

        assert isinstance(new_widget, InstanceWidget)

        if new_widget not in [x for x in self.scene().items()
                              if isinstance(x, InstanceWidget)]:
            self.scene().addItem(new_widget)
            new_widget.setZValue(5)  # Foreground of connections

        # Position given is middle of widget. Convert to top-left corner and set as widget's position.
        new_widget.setPos(x_pos - (new_widget.preferredSize().width() / 2),
                          y_pos - (new_widget.preferredSize().height() / 2))

    def remove_instance_widget(self, old_widget):
        """
        Remove widget from scene. (Effectively delete widget)
        :param old_widget: widget to be deleted.
        """

        # Remove from vector list
        self.widget_instances.remove(old_widget)

        # Remove from scene
        scene = self.scene()
        assert isinstance(scene, QtWidgets.QGraphicsScene)
        scene.removeItem(old_widget)

    # -- Connection Methods --

    def create_connection_widget(self, connection, from_instance, from_interface, to_instance, to_interface):
        """
        Create connection widget from the given model equivalents
        :param connection: camkes.ast.Connection object to be passed to
        :param from_instance: The camkes.ast.Instance on the From side.
        :param from_interface: The camkes.ast.Interface associated with the From Instance
        :param to_instance: The camkes.ast.Instance on the To side.
        :param to_interface: The camkes.ast.Interface associated with the To Instance
        :return: ConnectionWidget object
        """

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

    def add_connection_widget(self, new_connection):
        """
        Add connection to scene
        :param new_connection: widget to be added
        """

        assert isinstance(new_connection, ConnectionWidget)
        self.scene().addItem(new_connection)
        new_connection.setZValue(4)  # Behind all instance widgets (but above hidden instances and connection)

    def clear_connection_widgets(self):
        """
        Remove all connections from scene. Effectively deleting all existing connections
        """

        scene = self.scene()
        assert isinstance(scene, QtWidgets.QGraphicsScene)

        for connection in self.connection_widgets:
            scene.removeItem(connection)  # Remove from scene
            connection.delete()  # Let connection do some cleaning up - (delete itself from the instance widgets)

        del self.connection_widgets[:]  # Delete all connections widgets from internal list

    # --- Layout Methods ---

    def layout_from_file(self):
        """
        Open layout file from the same location as the .camkes file
        """

        # Attempt to open layout file.
        with open("%s.visualCAmkES.layout" % self.get_root_location(), 'r') as layout_file:
            # Load dictionaries (json format) from file.
            json_input = json.load(layout_file)

            for widget in self.widget_instances:
                assert isinstance(widget, InstanceWidget)

                # Get attributes for specific widget
                attributes = json_input.get(widget.name)

                # If widget doesn't exist in file, create an attribute with empty dictionary
                if attributes is None:
                    attributes = {}

                position = attributes['position']
                if position is not None:
                    assert isinstance(position, list)
                    # Reposition widget to new position
                    self.reposition_instance_widget(widget, position[0], position[1])
                else:
                    # If position doesn't exist
                    self.reposition_instance_widget(widget, self.geometry().x() / 2, self.geometry().y() / 2)

                if attributes['hidden'] is not None:
                    widget.hidden = attributes['hidden']

        self.update_view()
        self.save_layout_to_file()

    def save_layout_to_file(self):
        """
        Update current view to file
        :return:
        """

        node_positions = {}
        for widget in self.widget_instances:
            assert isinstance(widget, InstanceWidget)
            attributes = {}

            # Load centre of widget into widget's position attribute
            position_array = [widget.pos().x() - (widget.preferredSize().width() / 2),
                              widget.pos().y() - (widget.preferredSize().height() / 2)]
            attributes['position'] = position_array

            attributes['hidden'] = widget.hidden

            node_positions[widget.name] = attributes

        file_location =  "%s.visualCAmkES.layout" % self.get_root_location()

        with open(file_location, 'w') as output:
            json.dump(node_positions, output, indent=4)

    def autolayout(self):
        """
        Using graphviz to layout the current graph to 'dot' layout.
        """

        # Create a empty graph
        graph_viz = Digraph(engine='dot')

        # For all instances, add a node, with it's size.
        for widget_instance in self.widget_instances:
            assert isinstance(widget_instance, InstanceWidget)

            if widget_instance.hidden:
                continue

            size = widget_instance.preferredSize()
            assert isinstance(size, QtCore.QSizeF)

            graph_viz.node(widget_instance.name, width=str(size.width() / 72.0),
                           height=str(size.height() / 72.0), shape="rect")

        # For all (not hidden) connections), connect the source and destination widgets with minimum length of 2 inches
        for connection in self.connection_widgets:
            assert isinstance(connection, ConnectionWidget)
            if not connection.hidden:
                graph_viz.edge(connection.source_instance_widget.name, connection.dest_instance_widget.name,
                               minlen=str(2))

        # Generate / Render graph into 'dot' format
        raw_dot_data = graph_viz.pipe('dot')
        print "Graphviz rendering... the following is the dot file from graphviz"
        print raw_dot_data

        # Read dot format (using pydotplus)
        dot_data = pydotplus.graph_from_dot_data(raw_dot_data)

        # Get graphviz height
        graph_attributes = dot_data.get_graph_defaults()

        height = 0

        for attribute_dict in graph_attributes:
            if not isinstance(attribute_dict, dict):
                continue

            if attribute_dict['bb'] is not None:
                rectange = Common.extract_numbers(attribute_dict['bb'])
                height = rectange[1][1] - rectange[0][1]

        # For all instances, apply new position to widgets.

        for instance_widget in self.widget_instances:
            assert isinstance(instance_widget, InstanceWidget)

            if instance_widget.hidden:
                continue

            # Get instance's name
            instance_name = instance_widget.name

            # Get the node representing this instance, and get its attributes
            node_list = dot_data.get_node(instance_name)

            if len(node_list) < 1:
                # Name may be quoted due to special characters
                quoted_name = '"%s"' % instance_name
                node_list = dot_data.get_node(quoted_name)

            assert len(node_list) == 1  # Should only be one node
            assert isinstance(node_list[0], pydotplus.Node)
            node_attributes_dict = node_list[0].get_attributes()

            # Extract position of the node
            node_position_list = Common.extract_numbers(node_attributes_dict['pos'])
            assert len(node_position_list) is 1  # Should only be one position
            node_position = node_position_list[0]

            self.reposition_instance_widget(instance_widget, x_pos=node_position[0],
                                            y_pos=math.fabs(height - node_position[1]))

        self.update_view()
        self.save_layout_to_file()

    # --- EVENTS ---

    # -- UI --

    def resizeEvent(self, resize_event):
        """
        When resizing happens, update the corner buttons to the right position.
        :param resize_event:
        """

        assert isinstance(resize_event, QtGui.QResizeEvent)
        super(GraphWidget, self).resizeEvent(resize_event)

        self.update_outer_ui()

    def update_view(self):
        """
        Updates the view to be position correctly. Currently resizes scene to minimum size required.
        """

        rect = self.sceneRect()
        assert isinstance(rect, QtCore.QRectF)

        smallest_x = 0
        smallest_y = 0
        largest_x = 0
        largest_y = 0

        # Goal is to find the top-left point and bottom-right point of the graph.
        # To find top-left - find the InstanceWidget on the most top-left corner
        # To find bottom-right - find the Instance widget on the most bottom-right (including widget itself)
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
        """
        Position all the bottom-right corner buttons in the right place.
        :return:
        """

        bottom_corner = self.geometry().bottomRight()

        zoom_in_position = bottom_corner - QtCore.QPoint(self.zoom_in_button.sizeHint().width(),
                                                         self.zoom_in_button.sizeHint().height()) \
                           - QtCore.QPoint(20, 40)  # 40 due to some weird behaviour with File Menus

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

    def close_context_menu(self):
        """
        Close context (right-click) menu
        """

        if self._context_menu is not None:
            self._context_menu.widget().close()

    # -- Mouse events --
    def mousePressEvent(self, mouse_event):
        """
        When mouse is pressed, handles the closing of context menu.
        :param mouse_event: QMouseEvent object
        """

        assert isinstance(mouse_event, QtGui.QMouseEvent)

        # Get scene position from global position
        scene_position = self.mapToScene(mouse_event.pos())

        item = self.scene().itemAt(scene_position, self.transform())

        # If not pressed on context menu, close the menu.
        if not isinstance(item, QtWidgets.QGraphicsProxyWidget):
            self.close_context_menu()
        elif not isinstance(item.widget(), QtWidgets.QMenu):
            self.close_context_menu()

        super(GraphWidget, self).mousePressEvent(mouse_event)

    def mouseDoubleClickEvent(self, mouse_event):
        # Get scene position from global position
        scene_position = self.mapToScene(mouse_event.pos())

        item = self.scene().itemAt(scene_position, self.transform())

        if mouse_event.button() == QtCore.Qt.LeftButton:
            # If item has property to show and edit

            if isinstance(item, PropertyInterface):
                self.property_widget_dock.setWidget(item.property_widget)
                self.property_widget_dock.setVisible(True)

    def mouseReleaseEvent(self, mouse_event):
        """
        When mouse is released, handles the saving of layout.
        :param mouse_event: QMouseEvent object
        """

        super(GraphWidget, self).mouseReleaseEvent(mouse_event)

        if self.ast:
            self.save_layout_to_file()

    # -- Button clicks --

    def show_all_components(self):
        """
        Unhide all hidden components.
        """

        for widget in self.widget_instances:
            widget.hidden = False

    def zoom_in(self):

        self.scale(1.1, 1.1)

    def zoom_out(self):

        self.scale(0.9, 0.9)

    def save_picture(self):
        """
        Invokes the GUI routine of saving of an image
        """

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

        if save_option_dialog.picture_type == save_option_dialog.PNG:
            file_filter = "Image (*.png)"
        elif save_option_dialog.picture_type == save_option_dialog.SVG:
            file_filter = "Scalable Vector Graphics (*.svg)"

        filename = QtWidgets.QFileDialog.getSaveFileName(caption="Save file",
                                                         directory=self.get_root_location(with_name=True),
                                                         filter=file_filter)

        image_location = filename[0]  # getSaveFileName returns a tuple. First index of tuple is the file name

        if image_location.rfind('.') != -1:
            image_location = image_location[:image_location.rfind('.')]

        if len(image_location) <= 0:
            # Image location is not valid
            return

        rect = self.sceneRect()
        rect.adjust(-50, -50, 50, 50)

        painter = QtGui.QPainter()

        if save_option_dialog.picture_type == save_option_dialog.PNG:
            image = QtGui.QImage(save_option_dialog.user_width,
                                 save_option_dialog.user_height,
                                 QtGui.QImage.Format_ARGB32)
            image.fill(QtCore.Qt.transparent)

            painter.begin(image)
            painter.setRenderHint(QtGui.QPainter.Antialiasing)
            self.scene().render(painter, source=rect)
            painter.end()

            image.save("%s.png" % image_location)

        elif save_option_dialog.picture_type == save_option_dialog.SVG:
            generator = QtSvg.QSvgGenerator()
            generator.setFileName("%s.svg" % image_location)
            generator.setSize(QtCore.QSize(rect.width(), rect.height()))
            # generator.setViewBox(rect)
            generator.setTitle(save_option_dialog.user_title)
            generator.setDescription(save_option_dialog.user_description)

            painter.begin(generator)
            painter.setRenderHint(QtGui.QPainter.Antialiasing)
            self.scene().render(painter, source=rect)
            painter.end()

        else:
            return

    # --- HELPER FUNCTIONS ---

    def random_color_generator(self):
        """

        :return:
        """

        if self._color_seed is None:
            self._color_seed = 0.9214

        color = QtGui.QColor()
        color = color.fromHslF(self._color_seed, 1, 0.78, 1)

        self._color_seed = (self._color_seed + 0.618033988749895) % 1

        return color

    def find_instance_widget(self, name):
        """

        :param name:
        :return:
        """

        for instance in self.widget_instances:
            assert isinstance(instance, InstanceWidget)
            if instance.name == name:
                return instance

        return None

    def get_root_location(self, with_name=False):
        """

        :param with_name:
        :return:
        """

        assembly = self.ast.assembly
        assert isinstance(assembly, Assembly)
        location = assembly.location
        assert isinstance(location, SourceLocation)

        if with_name:
            return location.filename[:location.filename.rfind('.')]
        else:
            find_slash = location.filename.rfind('/')
            if find_slash == -1:
                find_slash = location.filename.rfind('\\')  # For windows
            return location.filename[:find_slash + 1]
