#!/usr/bin/env python
# -*- coding: utf-8 -*-
import re


def extract_numbers(list_of_tuples_stringnumbers):  # TODO: consider renaming list_of_tuples_...

        result = re.findall("([-+]?\d+[.]?\d*)[,]([-+]?\d+[.]?\d*)", list_of_tuples_stringnumbers)

        new_list = list()
        for next_tuple in result:
            converted_tuple = (float(next_tuple[0]), float(next_tuple[1]))
            new_list.append(converted_tuple)

        return new_list