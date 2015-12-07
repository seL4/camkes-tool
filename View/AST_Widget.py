#!/usr/bin/env python
# -*- coding: utf-8 -*-

from gi.repository import Gtk
import cairo

from camkes.ast.base import ASTObject


class ASTWidget(Gtk.DrawingArea):
    def __init__(self, ast_object):
        super(ASTWidget, self).__init__()
        self.add_child(Gtk.Label("Hello"))
