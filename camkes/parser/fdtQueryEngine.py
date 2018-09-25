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
#
import argparse

import six
import re
import logging
import pyfdt.pyfdt
from camkes.parser import Query

from .exception import  DtbBindingError, DtbBindingQueryFormatError, \
                        DtbBindingNodeLookupError, DtbBindingSyntaxError, \
                        DtbBindingTypeError, DtbBindingNotImplementedError


class FdtQueryEngine:
    """
    This class is responsible for wrapping around an instance of pyfdt and
    implementing a querying engine on top of it which can query for device nodes
    by path, alias and by matching against device properties.
    """
    def __init__(self, parsed_fdt):
        """
        The constructor takes an initialized instance of the fdt parser library
        for internal use.
        """
        if not parsed_fdt or not isinstance(parsed_fdt, pyfdt.pyfdt.Fdt):
            raise DtbBindingTypeError("fdt_parser expects an instance of class "
                                      "pyfdt.Fdt");

        self.parsed_fdt = parsed_fdt

    def _match_node_by_alias(self, alias):
        """
        Looks up an alias node by looking inside of /aliases for a subnode with
        the name passed in "alias".
        @param alias        Name of an alias you want to look for.
        @param include_consume_nodes
        """
        fdt_root = self.parsed_fdt.get_rootnode()
        try:
            aliases_idx = fdt_root.index("aliases")
        except ValueError:
            # Rethrow with a human readable error message
            raise DtbBindingNodeLookupError("Request to lookup alias \"%s\" in "
                                            "a DTB with no /aliases node!"
                                            % alias)

        aliases = fdt_root.subdata[aliases_idx]
        try:
            ret_idx = aliases.index(alias)
        except ValueError:
            raise DtbBindingNodeLookupError("DTB does not contain an alias "
                                             "named %s!"
                                             % alias)

        prop = aliases.subdata[ret_idx]
        # An alias property must be a path string to another node.
        assert isinstance(prop, pyfdt.pyfdt.FdtPropertyStrings)
        # An alias shouldn't be a multi-string
        assert len(prop.strings) == 1
        # From here we have the path to the node the user wanted. Look it up.
        ret = self._match_nodes_by_path(re.escape(prop.strings[0]));
        if not len(ret):
            raise DtbBindingNodeLookupError("Alias %s maps to path %s, but "
                                            "that path resolves to nothing."
                                            % (alias, prop.strings[0]))

        if len(ret) > 1:
            raise DtbBindingNodeLookupError("Alias %s maps to path %s, but "
                                            "that path resolves to multiple "
                                            "results."
                                            % (alias, prop.strings[0]))
        return ret

    def _match_nodes_by_path(self, qstring):
        """
        Parses a single camkes_dts_path query string.

        @param[in] qstring                The query string
                                          The query string can contain Regex
                                          match operators.
        @return An array of nodes whose paths match the query string.
        """
        fdt_root = self.parsed_fdt.get_rootnode()
        fdt_iter = fdt_root.walk()
        matches = []

        qstring = r"" + qstring
        try:
            regex = re.compile(qstring)
        except re.error:
            # Rethrow with a more user friendly message to help the dev debug
            raise DtbBindingQueryFormatError("Input query string \"%s\" is not "
                                             "a valid regex."
                                              % qstring)

        # Try the regex against each path from the DTB and build a list of those
        # node paths which match.
        for node in fdt_iter:
            currpath = r"" + node[0]
            currnode = node[1]
            # We don't want property nodes -- only device nodes.
            if not isinstance(currnode, pyfdt.pyfdt.FdtNode):
                continue

            if not regex.search(currpath):
                continue

            matches.append(currnode)

        return matches

    @staticmethod
    def _compare_node_property_as_string(prop, p_key, val):
        """ Negative index into the string array is how the the "*" operator is
            implemented internally.
        """
        if p_key["index"] < 0:
            assert isinstance(val, list)
            return (len(prop.strings) == len(val)) and (prop.strings == val)

        else:
            if not isinstance(val, six.string_types):
                raise DtbBindingTypeError("Property %s is a string property, so "
                                          "values matched against it must also be "
                                          "strings"
                                          % prop.get_name())

            if not len(prop.strings) > p_key["index"]:
                return False

            return prop.strings[p_key["index"]] == val

    @staticmethod
    def _compare_node_property_as_integers(prop, p_key, val, size):
        """ Negative index into the string array is how the the "*" operator is
            implemented internally.
        """
        if p_key["index"] < 0:
            assert isinstance(val, list)
            if size == "byte":
                for i in val:
                    assert isinstance(i, six.integer_types)
                    if not -128 <= i <= 127:
                        raise DtbBindingTypeError("Value %d exceeds size of a "
                                                  "byte..."
                                                  % i)

            return (len(prop.words) == len(val)) \
                and (prop.words == val)

        else:
            if not isinstance(val, six.integer_types):
                raise DtbBindingTypeError("Property %s is a string property, so "
                                          "values matched against it must also be "
                                          "strings"
                                          % prop.get_name())

            if not len(prop.words) > p_key["index"]:
                return False

            return prop.words[p_key["index"]] == val

    @staticmethod
    def _compare_node_property_as_null(prop, p_key, val):
        if not val:
            return True
        if isinstance(val, six.string_types) and val == "":
            return True
        if isinstance(val, six.integer_types) and val == 0:
            """ We're being very lenient here, but allow a 0-value to count as
                a match against a property which is unset.
            """
            return True

        return False

    def _compare_node_property_to_attr(self, prop, p_key, val):
        if isinstance(prop, pyfdt.pyfdt.FdtPropertyStrings):
            result = self._compare_node_property_as_string(prop, p_key, val)
        elif isinstance(prop, pyfdt.pyfdt.FdtPropertyWords):
            result = self._compare_node_property_as_integers(prop, p_key, val, "word")
        elif isinstance(prop, pyfdt.pyfdt.FdtNop):
            result = self._compare_node_property_as_null(prop, p_key, val)
        elif isinstance(prop, pyfdt.pyfdt.FdtPropertyBytes):
            result = self._compare_node_property_as_integers(prop, p_key, val, "byte")
        else:
            raise DtbBindingTypeError("Not sure how to handle FDT property %s "
                                      "with unexpected type %s."
                                      % (str(prop), type(prop)))

        return result

    @staticmethod
    def _parse_key(key_str):
        attr = key_str
        index = 0

        lbrace_idx = key_str.find('[')
        if lbrace_idx != -1:
            """ If we find an opening brace, assume that there is indexing
                notation in the key. Extract the index.
            """
            # The right brace must be encountered *after* the the left one.
            rbrace_idx = key_str[lbrace_idx + 1:].find(']')
            if rbrace_idx == -1:
                raise DtbBindingSyntaxError("DTB Binding attribute has "
                                            "incomplete brace notation!")

            idx_str = key_str[lbrace_idx + 1:]
            idx_str = idx_str[:rbrace_idx]
            idx_str = idx_str.strip(' ')
            if idx_str == "*":
                # For the "*" index operator, we represent it internally as -1.
                index = -1
            else:
                try:
                    if idx_str.startswith("0x"):
                        index = int(idx_str, 16)
                    else:
                        index = int(idx_str, 10)
                except ValueError:
                    # Rethrow it with a human-readable error string.
                    raise DtbBindingTypeError("Invalid integer index %s in "
                                              "key %s!"
                                              % (idx_str, key_str))

            attr = key_str[:lbrace_idx]

        return {"key": attr, "index": index}

    @staticmethod
    def _get_matching_prop_from_node(node_props, parsed_key):
        matching_props = [prop for prop in node_props
            if prop.get_name() == parsed_key["key"]]

        if len(matching_props) == 0:
            return None

        if len(matching_props) > 1:
            raise DtbBindingSyntaxError("Input DTB file has a node which has "
                                        "two properties having the same name!")

        return matching_props[0]

    def _match_node_by_attrs(self, node, attr_dict):
        """
        Compare a pyfdt.FdtNode against a set of attrs given as a dict. If all
        the the node matches all the attrs and values, returns true.

        @param[in] node         The pyfdt.FdtNode which is going to be scanned.
        @param[in] attr_dict    The attributes which "node" must be compared
                                against.
        @return True if (ALL keys in "attr_dict" exist in "node") AND
            (ALL values in "attr_dict" match their homologues in "node").
        """
        node_props = [sub for sub in node.subdata
            if isinstance(sub, pyfdt.pyfdt.FdtProperty)]

        for key, val in attr_dict.items():
            """ We allow things like indexing in the lvalue key
                (e.g: 'regs[0]'), so we have to potentially extract the raw key
                from an key with indexed notation attached to it.
            """
            parsed_key = self._parse_key(key)
            matching_prop = self._get_matching_prop_from_node(node_props,
                                                              parsed_key)

            if not matching_prop:
                return False

            # The node must *both* have the attribute, AND have its value match.
            if not self._compare_node_property_to_attr(matching_prop,
                                                       parsed_key, val):
                return False

        return True

    def _match_nodes_by_attrs(self, attr_dict, search_data_set):

        # If there are no attrs to compare against, exit early.
        if not len(attr_dict.keys()):
            return []

        matches = []

        if search_data_set and len(search_data_set):
            """ If the caller has already narrowed down the set of nodes s/he
                wants us to search, then use that data set:
            """
            for node in search_data_set:
                assert isinstance(node, pyfdt.pyfdt.FdtNode)
                if self._match_node_by_attrs(node, attr_dict):
                    matches.append(node)
        else:
            # Else search all nodes in the entire FDT
            fdt_root = self.parsed_fdt.get_rootnode()
            fdt_iter = fdt_root.walk()

            for node in fdt_iter:
                # We don't want property nodes here either; just device nodes.
                if not isinstance(node[1], pyfdt.pyfdt.FdtNode):
                    continue

                if self._match_node_by_attrs(node[1], attr_dict):
                    matches.append(node[1])

        return matches

    def query(self, attr_dict):
        assert isinstance(attr_dict, dict)

        """ If there is an alias binding query which we can use, then try that
            first since those should only resolve to a single result.
        """
        if ("camkes_dts_alias" in attr_dict) or ("camkes_dtb_alias" in attr_dict):
            # Force the user to choose one; don't allow them to supply both.
            if ("camkes_dts_alias" in attr_dict) and ("camkes_dtb_alias" in attr_dict):
                raise DtbBindingQueryFormatError("Please choose between "
                                                 "camkes_dts_alias and "
                                                 "camkes_dtb_alias!")

            if "camkes_dts_alias" in attr_dict:
                alias_key = "camkes_dts_alias"
            else:
                alias_key = "camkes_dtb_alias"

            """ Since camkes_dts_alias is meant to be an unambiguous match
                against a single node, do not try to resolve other attributes
                if the user already supplied camkes_dts_alias.

                Instead, assume that they meant to have a specific node
                matched, and that it is a mistake on their part that other
                attributes were also supplied.
            """
            other_attrs = [key for key in attr_dict if key != alias_key]
            if len(other_attrs):
                logging.warn("Silently ignoring other attributes supplied in "
                             "DTB binding since %s should be sufficient.\n"
                             "Ignored attributes were: %s."
                             % (alias_key, str(other_attrs)))

            """ An alias match, if found, is an unambiguous match. No need to
                do any further searching.
            """
            return self._match_node_by_alias(alias_value)

        """ If there is a path query which we can use to cut the search set down,
            get that out of the way first.
        """
        path_matches = []
        if ("camkes_dts_path" in attr_dict) or ("camkes_dtb_path" in attr_dict):
            # Force the user to supply one; Don't allow them to set both.
            if ("camkes_dts_path" in attr_dict) and ("camkes_dtb_path" in attr_dict):
                raise DtbBindingQueryFormatError("Please choose between "
                                                 "camkes_dts_path and "
                                                 "camkes_dtb_path!")

            # See which one they used and use that to index into the dict.
            if "camkes_dts_path" in attr_dict:
                path_key = "camkes_dts_path"
            else:
                path_key = "camkes_dtb_path"

            path_matches = self._match_nodes_by_path(attr_dict[path_key],
                                                     include_consumed_nodes)
            """ Remove the path attribute so it isn't used during property
                matching
            """
            attr_dict.pop(path_key)

        if not len(attr_dict):
            return path_matches

        """ Now, using the narrowed down results from the path query, attempt to
            match based on the properties.
        """
        property_matches = self._match_nodes_by_attrs(attr_dict, path_matches)

        return property_matches


class DtbMatchQuery(Query):
    """Convert a dtb query into a dictionary of results from the device tree"""
    def __init__(self):
        self.dtb = None

    def resolve(self, *args):
        # for now just return a list of empty strings as the result
        return [""]

    @staticmethod
    def get_parser():
        parser = argparse.ArgumentParser('dtb')
        parser.add_argument('--dtb',
                            type=str,
                            help='Flattened device tree blob (.dtb) to query for device tree properties.',
                            required=True)
        return parser

    def check_options(self):
        try:
            with open(self.options.dtb, 'rb') as dtb_file:
                self.dtb = FdtBlobParse(dtb_file).to_fdt()
        except:
            logging.fatal("Failed to parse dtb file {0}".format(self.options.dtb.name))
    @staticmethod
    def get_query_name():
        return "dtb"

    def get_deps(self):
        return [self.options.dtb]
