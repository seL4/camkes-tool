#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

import argparse,os

from camkes.parser.parser import Parser
import camkes.ast

class ASTModel:

    def __init__(self):
        # Nothing to do for initialization
        pass

    '''
    A static method that returns an LiftedAST object given a path to the camkes file
    '''
    @staticmethod
    def get_ast(path_to_camkes_file, import_paths=None):
        """
        Talks to the parser and gets an AST representation of the camkes ADL code
        :param path_to_camkes_file: Path to .camkes file
        :return: LiftedAST object
        """

        args = argparse.ArgumentParser()
        args.add_argument('--import-path', '-I', help='Add this path to the list of paths to '
                                                           'search for built-in imports. That is, add it to the list '
                                                           'of directories that are searched to find the file "foo" '
                                                           'when encountering an expression "import <foo>;".',
                               action='append', default=[])

        import_arguments = ["--import-path",
                            os.path.join(os.path.dirname(os.path.abspath(__file__)),'../../../include/builtin')]

        if import_paths is not None:
            for a in import_paths:
                import_arguments.extend(["--import-path",
                                         a])

        parse_args = args.parse_args(import_arguments)

        camkes_parser = Parser(parse_args)
        ast, _read = camkes_parser.parse_file(path_to_camkes_file)

        return ast

    @staticmethod
    def find_instance(list_of_ast_items, instance_name):
        """
        Find the instance (camkes.ast.Instance object) from list of instances give.
        :param list_of_ast_items: list of camkes.ast.* objects
        :param instance_name: The name of instance to looking for.
        :return: camkes.ast.Instance object if found, None otherwise.
        """
        for instance_object in list_of_ast_items:
            if not isinstance(instance_object, camkes.ast.Instance):
                continue
            assert isinstance(instance_object, camkes.ast.Instance)
            if instance_name == instance_object.name:
                return instance_object

        return None

    @staticmethod
    def find_component(list_of_ast_items, component_name):
        """
        Find the component (camkes.ast.Component) from list of AST objects items give.
        :param list_of_ast_items: list of camkes.ast.* objects
        :param component_name: The name of component type to looking for.
        :return: camkes.ast.Component object if found, None otherwise
        """
        for item in list_of_ast_items:
            if not isinstance(item, camkes.ast.Component):
                continue
            assert isinstance(item, camkes.ast.Component)
            if item.name == component_name:
                return item

        return None

    # IDEAS:
    # Deleting connections with multiple froms, to:
    # User will delete a specific from - to. When removing the "from" in the connection, make sure there aren't
    # other "tos" in the connection (other than the "to" being deleted). Same vice-versa
