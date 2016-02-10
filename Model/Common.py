#!/usr/bin/env python
# -*- coding: utf-8 -*-
import re

Event="Event"
Procedure="Procedure"
Dataport="Dataport"


def extract_numbers(list_of_tuples_string_numbers):

        result = re.findall("([-+]?\d+[.]?\d*[eE]*[-+]*\d*)[,]([-+]?\d+[.]?\d*[eE]*[-+]*\d*)",
                            list_of_tuples_string_numbers)

        new_list = list()
        for next_tuple in result:
            converted_tuple = (float(next_tuple[0]), float(next_tuple[1]))
            new_list.append(converted_tuple)

        return new_list
