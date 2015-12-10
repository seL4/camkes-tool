#!/usr/bin/env python
# -*- coding: utf-8 -*-

import math

from gi.repository import Gtk
import cairo


class ConnectionWidget(Gtk.DrawingArea):
    def __init__(self):
        super(ConnectionWidget, self).__init__()
        self.connect("draw", self.draw_callback)

    @staticmethod
    def draw_callback(canvas_widget, cairo_context):
        print "draw"

        assert isinstance(canvas_widget, Gtk.Widget)

        canvas_width = canvas_widget.get_allocated_width()
        canvas_height = canvas_widget.get_allocated_height()

        print "Canvas width: " + str(canvas_width) + " and canvas height: " + str(canvas_height)

        assert isinstance(cairo_context, cairo.Context)

        cairo_context.set_source_rgb(0,0,0)
        cairo_context.set_line_width(0.5)

        cairo_context.move_to(0, canvas_height/2)
        cairo_context.line_to(canvas_width, canvas_height/2)
        cairo_context.stroke()
