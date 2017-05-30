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
from multiprocessing import Pool
from multiprocessing import Queue
import os
import sys
import textwrap

from nltk.sem.logic import LogicalExpressionException

from ccg2lambda_tools import assign_semantics_to_ccg
from semantic_index import SemanticIndex

SEMANTIC_INDEX=None
kMaxTasksPerChild=None
ARGS=None

def main(args = None):
    global SEMANTIC_INDEX
    global ARGS
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
    parser.add_argument("--ncores", nargs='?', type=int, default="3",
        help="Number of cores for multiprocessing.")
    ARGS = parser.parse_args()
      
    if not os.path.exists(ARGS.templates):
        print('File does not exist: {0}'.format(ARGS.templates))
        sys.exit(1)
    if not os.path.exists(ARGS.ccg):
        print('File does not exist: {0}'.format(ARGS.ccg))
        sys.exit(1)
    
    logging.basicConfig(level=logging.WARNING)

    SEMANTIC_INDEX = SemanticIndex(ARGS.templates)

    parser = etree.XMLParser(remove_blank_text=True)
    root = etree.parse(ARGS.ccg, parser)

    sentences = root.findall('.//sentence')
    # from pudb import set_trace; set_trace()
    sem_nodes = semantic_parse_sentences(sentences, ARGS.ncores)
    for sentence, sem_node in zip(sentences, sem_nodes):
        sentence.append(sem_node)

    root_xml_str = serialize_tree(root)
    with codecs.open(ARGS.sem, 'wb') as fout:
        fout.write(root_xml_str)

def semantic_parse_sentences(sentences, ncores=1):
    if ncores <= 1:
        sem_nodes = semantic_parse_sentences_seq(sentences)
    else:
        sem_nodes = semantic_parse_sentences_par(sentences, ncores)
    return sem_nodes

def semantic_parse_sentences_par(sentences, ncores=3):
    pool = Pool(processes=ncores, maxtasksperchild=kMaxTasksPerChild)
    sentences_strs = [etree.tostring(s) for s in sentences]
    sem_nodes = pool.map(semantic_parse_sentence, sentences_strs)
    pool.close()
    pool.join()
    return sem_nodes

def semantic_parse_sentences_seq(sentences):
    sem_nodes = []
    for sentence in sentences:
        sentence_str = etree.tostring(sentence)
        sem_node = semantic_parse_sentence(sentence_str)
        sem_nodes.append(sem_node)
    return sem_nodes

def semantic_parse_sentence(sentence_str):
    """
    `sentence` is an lxml tree with tokens and ccg nodes.
    It returns an lxml semantics node.
    """
    sentence = etree.fromstring(sentence_str)
    sem_node = etree.Element('semantics')
    try:
        sem_node.set('status', 'success')
        tree_index = 1
        if ARGS.gold_trees:
            tree_index = int(sentence.get('gold_tree', '0')) + 1
        # from pudb import set_trace; set_trace()
        sem_tree = assign_semantics_to_ccg(
            sentence, SEMANTIC_INDEX, tree_index)
        sem_node.set('root',
            sentence.xpath('./ccg[{0}]/@root'.format(tree_index))[0])
        filter_attributes(sem_tree)
        sem_node.extend(sem_tree.xpath('.//descendant-or-self::span'))
        print('.', end='', file=sys.stdout)
    except LogicalExpressionException as e:
        sem_node.set('status', 'failed')
        logging.error('An error occurred: {0}\nSentence: {1}'.format(
            e, etree.tostring(sentence, encoding='utf-8', pretty_print=True).decode('utf-8')))
        print('x', end='', file=sys.stdout)
    return sem_node

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
