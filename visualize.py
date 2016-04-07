#!/usr/bin/python3
# -*- coding: utf-8 -*-
#
#  Copyright 2015 Pascual Martinez-Gomez
#
#  Licensed under the Apache License, Version 2.0 (the "License");
#  you may not use this file except in compliance with the License.
#  You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
#  Unless required by applicable law or agreed to in writing, software
#  distributed under the License is distributed on an "AS IS" BASIS,
#  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#  See the License for the specific language governing permissions and
#  limitations under the License.

import argparse
import logging
from lxml import etree
import os
import textwrap

from visualization_tools import convert_doc_to_mathml

def main(args = None):
    DESCRIPTION=textwrap.dedent("""\
            Prints graphically in HTML the CCG tree. If <semantics> content
            is also present in the XML file, then logical formulas appear
            below the syntactic categories to show the semantic composition.
            The input file with the CCG tree should follow Jigg's format:
            https://github.com/mynlp/jigg
      """)

    parser = argparse.ArgumentParser(
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=DESCRIPTION)
    parser.add_argument("trees_xml")
    args = parser.parse_args()
      
    if not os.path.exists(args.trees_xml):
        print('File does not exist: {0}'.format(args.trees_xml))
    
    logging.basicConfig(level=logging.WARNING)

    parser = etree.XMLParser(remove_blank_text=True)
    doc = etree.parse(args.trees_xml, parser)

    html_str = convert_doc_to_mathml(doc)
    print(html_str)

if __name__ == '__main__':
    main()
