#!/usr/bin/env python
# -*- coding: utf-8 -*-

from gi.repository import Gtk
import cairo

from camkes.ast.base import ASTObject

from Controller.base_controller import Controller


class ASTWidget(Gtk.Box):

    @property
    def widget_controller(self):
        return self._widget_controller

    @widget_controller.setter
    def widget_controller(self, value):
        assert issubclass(value.__class__, Controller) or isinstance(value, Controller)

    def __init__(self, ast_object, widget_controller):
        super(ASTWidget, self).__init__()
        self._widget_Controller = widget_controller

        self.add()
