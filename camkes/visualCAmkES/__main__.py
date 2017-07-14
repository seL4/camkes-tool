#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2017, Data61
# Commonwealth Scientific and Industrial Research Organisation (CSIRO)
# ABN 41 687 119 230.
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(DATA61_BSD)

import sys, os

sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../'))
sys.path.append(os.path.dirname(os.path.abspath(__file__)))

from PyQt5 import QtWidgets, QtGui

from Controller.graph_controller import GraphController

def main(argv, out, err):
    '''
    This is the main function for the program. It allows the user to start the module by going "python visualCAmkES"

    :param argv: sys.argv - Arguments to the function.
    :param out: sys.stdout - Unused
    :param err: sys.stderr - Unused
    :return
    '''

    # Create a Qt app, set the name and window icon.
    app = QtWidgets.QApplication(argv)
    app.setApplicationName("VisualCAmkES")
    app.setWindowIcon(QtGui.QIcon(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'Assests/VisualCAmkES.png')))

    # A good place to do any argument parsing.

    # Create a GraphController and start the application
    new_controller = GraphController()
    new_controller.show()

    app.exec_()

if __name__ == '__main__':
    sys.exit(main(sys.argv, sys.stdout, sys.stderr))
