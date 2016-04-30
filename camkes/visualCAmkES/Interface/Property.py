#!/usr/bin/env python
# -*- coding: utf-8 -*-

#import math, six

# from PyQt5 import QtGui, QtWidgets, QtCore
# Can be better done with https://www.python.org/dev/peps/pep-3119/


class PropertyInterface:
    @property
    def property_widget(self):
        raise NotImplementedError
