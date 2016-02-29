#!/usr/bin/env python
# -*- coding: utf-8 -*-

import argparse,os

from camkes.parser.parser import Parser
import camkes.ast


class ASTModel:

    def __init__(self):
        pass

    '''
    A static method that returns an LiftedAST object given a path to the camkes file
    '''
    @staticmethod
    def get_ast(path_to_camkes_file):
        args = argparse.ArgumentParser()
        args.add_argument('--import-path', '-I', help='Add this path to the list of paths to '
                                                           'search for built-in imports. That is, add it to the list '
                                                           'of directories that are searched to find the file "foo" '
                                                           'when encountering an expression "import <foo>;".',
                               action='append', default=[])

        parse_args = args.parse_args(["--import-path",
                                os.path.join(os.path.dirname(os.path.abspath(__file__)),'../../../include/builtin')])

        print parse_args.__class__

        camkes_parser = Parser(parse_args)
        ast, _read = camkes_parser.parse_file(path_to_camkes_file)


        return ast

    @staticmethod
    def find_instance(instance_list, instance_name):

        for instance_object in instance_list:
            assert isinstance(instance_object, camkes.ast.Instance)
            if instance_name == instance_object.name:
                return instance_object

        return None

    @staticmethod
    def find_component(list_of_ast_items, component_name):

        for item in list_of_ast_items:
            if not isinstance(item, camkes.ast.Component):
                continue
            assert isinstance(item, camkes.ast.Component)
            if item.name == component_name:
                return item

        return None

    # TODO deleting connections with multiple froms, to:
    # User will delete a specific from - to. When removing the "from" in the connection, make sure there aren't other "tos"
    # in the connection (other than the "to" being deleted). Same vice-versa
