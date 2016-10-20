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

from __future__ import print_function

import argparse
import codecs
import logging
from lxml import etree
import os
import sys
import textwrap

from nltk.sem.logic import LogicalExpressionException

from ccg2lambda_tools import assign_semantics_to_ccg
from semantic_index import SemanticIndex

def main(args = None):
    DESCRIPTION=textwrap.dedent("""\
            categories_template.yaml should contain the semantic templates
              in YAML format.
            parsed_sentence.xml contains the CCG-parsed sentences.
            If --arbi-types is specified, then the arbitrary specification of
              types is enabled, thus using the argument as the field of the semantic
              template that is used. E.g, by specifying "--arbi-types coq_type"
              and a semantic template:
            - semantics: \P x.P(x)
              category: NP
              coq_type: Animal
            The type "Animal" will be used for this expression. Otherwise,
            types of the sem/logic module of NLTK are used.
      """)

    parser = argparse.ArgumentParser(
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=DESCRIPTION)
    parser.add_argument("ccg")
    parser.add_argument("templates")
    parser.add_argument("sem")
    parser.add_argument("--arbi-types", action="store_true", default=False)
    parser.add_argument("--gold_trees", action="store_true", default=True)
    args = parser.parse_args()
      
    if not os.path.exists(args.templates):
        print('File does not exist: {0}'.format(args.templates))
        sys.exit(1)
    if not os.path.exists(args.ccg):
        print('File does not exist: {0}'.format(args.ccg))
        sys.exit(1)
    
    logging.basicConfig(level=logging.WARNING)

    semantic_index = SemanticIndex(args.templates)

    parser = etree.XMLParser(remove_blank_text=True)
    root = etree.parse(args.ccg, parser)

    for sentence in root.findall('.//sentence'):
        sem_node = etree.Element('semantics')
        try:
            sem_node.set('status', 'success')
            tree_index = 1
            if args.gold_trees:
                tree_index = int(sentence.get('gold_tree', '0')) + 1
            sem_tree = assign_semantics_to_ccg(
                sentence, semantic_index, tree_index)
            sem_node.set('root',
                sentence.xpath('./ccg[{0}]/@root'.format(tree_index))[0])
            filter_attributes(sem_tree)
            sem_node.extend(sem_tree.xpath('.//descendant-or-self::span'))
        except LogicalExpressionException:
            sem_node.set('status', 'failed')
        sentence.append(sem_node)

    root_xml_str = serialize_tree(root)
    with codecs.open(args.sem, 'wb') as fout:
        fout.write(root_xml_str)

keep_attributes = set(['id', 'child', 'sem', 'type'])
def filter_attributes(tree):
    if 'coq_type' in tree.attrib and 'child' not in tree.attrib:
        sem_type = \
            tree.attrib['coq_type'].lstrip('["Parameter ').rstrip('."]')
        if sem_type:
            tree.attrib['type'] = sem_type
    attrib_to_delete = [a for a in tree.attrib.keys() if a not in keep_attributes]
    for a in attrib_to_delete:
        del tree.attrib[a]
    for child in tree:
        filter_attributes(child)
    return

def serialize_tree(tree):
    tree_str = etree.tostring(
        tree, xml_declaration=True, encoding='utf-8', pretty_print=True)
    return tree_str

if __name__ == '__main__':
    main()
