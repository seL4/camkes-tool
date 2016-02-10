#!/usr/bin/env python
# -*- coding: utf-8 -*-

import sys, os

sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../'))
sys.path.append(os.path.dirname(os.path.abspath(__file__)))

from PyQt5 import QtWidgets

from Controller.graph_controller import GraphController


def main(argv, out, err):
    app = QtWidgets.QApplication(argv)

    # new_controller = GraphController("/home/sthasarathan/Documents/camkes-newExample/apps/complex/complex.camkes")
    new_controller = GraphController()

    # new_controller = GraphController("/home/sthasarathan/Documents/CAMKES-APPS/camkes-kitty-HDDMA/apps/bilbyfs/bilbyfs.camkes")
    # new_controller = GraphController("/home/sthasarathan/Documents/test/cddc/apps/cddc/cddc.camkes")
    # new_controller = GraphController("/home/sthasarathan/Documents/quadcopter/quadcopter-next/apps/quadcopter/quadcopter.camkes")

    new_controller.show()

    app.exec_()

    

if __name__ == '__main__':
    sys.exit(main(sys.argv, sys.stdout, sys.stderr))
