#!/usr/bin/env python
# -*- coding: utf-8 -*-

# Can be better done with https://www.python.org/dev/peps/pep-3119/

class PropertyInterface(object):
    @property
    def property_widget(self):
        raise NotImplementedError
