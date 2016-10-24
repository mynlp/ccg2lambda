#!/usr/bin/python3
# -*- coding: utf-8 -*-
#
#  Copyright 2016 Pascual Martinez-Gomez
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

from __future__ import print_function

import argparse
import codecs
import logging
from lxml import etree
import os
import sys
import textwrap

def jigg2transccg_doc(xml_doc):
    for token in xml_doc.xpath('//token'):
        token.set('surf', token.get('form'))
        token.set('base', token.get('lemma'))
        del token.attrib['form']
        del token.attrib['lemma']
    for span in xml_doc.xpath('//ccg/span'):
        span.set('category', span.get('symbol'))
        children_str = span.get('children')
        if not 'sp' in children_str and not ' ' in children_str:
            # This is a terminal.
            span.set('terminal', children_str)
        else:
            span.set('child', children_str)
        del span.attrib['children']
    return xml_doc

def main(args = None):
    DESCRIPTION=textwrap.dedent("""\
            Transform a Jigg XML file into a transccg format.
            It prints the XML output tree to standard output.
      """)

    parser = argparse.ArgumentParser(
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=DESCRIPTION)
    parser.add_argument("jigg_fname", help="Jigg XML filename with CCG trees.")
    # parser.add_argument("transccg_fname", help="Jigg XML filename with CCG trees.")
    args = parser.parse_args()
      
    if not os.path.exists(args.jigg_fname):
        print('File does not exist: {0}'.format(args.jigg_fname), file=sys.stderr)
        parser.print_help(file=sys.stderr)
        sys.exit(1)
    
    logging.basicConfig(level=logging.WARNING)

    parser = etree.XMLParser(remove_blank_text=True)
    jigg_doc = etree.parse(args.jigg_fname, parser)
    transccg_doc = jigg2transccg_doc(jigg_doc)
    # from pudb import set_trace; set_trace()

    # root_xml_str = serialize_tree(transccg_doc)
    # with codecs.open(args.transccg_fname, 'wb') as fout:
    #     fout.write(root_xml_str)

    # with codecs.open(args.transccg_fname, 'wb', 'utf-8') as fout:
    #   transccg_doc.write(fout, pretty_print=True, encoding='utf-8')
    result = etree.tostring(transccg_doc, encoding='utf-8', pretty_print=True)
    print(result.decode('utf-8'))
    # print(result)

def serialize_tree(tree):
    tree_str = etree.tostring(
        tree, xml_declaration=True, encoding='utf-8', pretty_print=True)
    return tree_str


if __name__ == '__main__':
    main()
