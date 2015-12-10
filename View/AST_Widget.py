#!/usr/bin/env python
# -*- coding: utf-8 -*-

from gi.repository import Gtk
import cairo
import math

from camkes.ast.base import ASTObject

from Controller.base_controller import Controller


class ASTWidget(Gtk.DrawingArea):

    @property
    def widget_controller(self):
        return self._widget_controller

    @widget_controller.setter
    def widget_controller(self, value):
        assert issubclass(value.__class__, Controller) or isinstance(value, Controller)

    def __init__(self): # , widget_controller, points):
        super(ASTWidget, self).__init__()
        # self._widget_Controller = widget_controller

        self.connect("draw", self.draw_callback)

        # self.points = points

    def draw_callback(self, cario_context, user_data):
        print "called"

        assert isinstance(cario_context, cairo.Context)

        width = self.get_allocated_width()
        height = self.get_allocated_height()

        cario_context.arc(width/2.0, height/2.0, min(width, height)/2.0, 0, 2*math.pi)

        cario_context.set_source_rgb(0,0,0)
        cario_context.fill()

        '''
        cario_context.set_source_rgb(0,0,0)
        cario_context.set_line_width(0.5)

        for point in self.points:
            cario_context.line_to(point[0], point[1])

        cario_context.stroke()
        '''