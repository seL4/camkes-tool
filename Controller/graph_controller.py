#!/usr/bin/env python
# -*- coding: utf-8 -*-

import sys
from base_controller import Controller
from gi.repository import Gtk


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

    def __init__(self):
        super(GraphController, self).__init__()
        self.root_widget = Gtk.DrawingArea()


def main():
    new_controller = GraphController()
    main_window = Gtk.Window()
    main_window.add(new_controller.root_widget)
    main_window.connect("delete-event", Gtk.main_quit)
    main_window.show_all()
    Gtk.main()


if __name__ == '__main__':
    sys.exit(main())
