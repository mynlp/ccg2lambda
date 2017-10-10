#!/usr/bin/python3
# -*- coding: utf-8 -*-
#
#  Copyright 2017 Pascual Martinez-Gomez
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
import json
from lxml import etree
import os
import sys
import textwrap

from semparse import serialize_tree

def relabel(root, label=None):
    if label is None:
        return root
    for ccg in root.xpath('./document/sentences/sentence/ccg'):
        ccg.set('id', '{0}_{1}'.format(label, ccg.get('id')))
        ccg.set('ccg_parser', label)
    for sem in root.xpath('./document/sentences/sentence/semantics'):
        sem.set('ccg_id', '{0}_{1}'.format(label, sem.get('ccg_id')))
        sem.set('ccg_parser', label)
    return root

def create_index(root):
    index = {doc.get('pair_id', None) : doc for doc in root.xpath('./document')}
    return index

def insert_nodes_by_tag(target, nodes, tag):
    assert isinstance(nodes, list)
    target_nodes = target.xpath('./' + tag)
    if not target_nodes:
        target.extend(nodes)
    else:
        insert_index = target.index(target_nodes[-1])
        for i, node in enumerate(nodes):
            target.insert(insert_index + i + 1, node)
    return

class Merger(object):
    """
    Merges XML RTE problems according to their pair_id.
    """

    def __init__(self):
        self.id2doc = None
        self.root = None
        self.xml = None

    def add(self, root, label=None):
        root = relabel(root, label)
        if self.root is None:
            self.xml = root
            self.root = root.getroot()
            self.id2doc = create_index(self.root)
        for doc in root.xpath('./document'):
            doc_id = doc.get('id', None)
            if doc_id is None:
                continue
            if doc_id not in self.id2doc:
                self.root.append(doc)
                self.id2doc[doc_id] = doc
            else:
                orig_doc = self.id2doc[doc_id]
                orig_sents = orig_doc.xpath('./sentences/sentence')
                new_sents = doc.xpath('./sentences/sentence')
                assert len(orig_sents) == len(new_sents), '%d vs. %d' % (len(orig_sents), len(new_sents))
                for orig_sent, new_sent in zip(orig_sents, new_sents):
                    new_ccgs = new_sent.xpath('./ccg')
                    if new_ccgs:
                        insert_nodes_by_tag(orig_sent, new_ccgs, 'ccg')
                    new_sems = new_sent.xpath('./semantics')
                    if new_sems:
                        insert_nodes_by_tag(orig_sent, new_sems, 'semantics')
        return

    def write(self, out_fname):
        xml_str = serialize_tree(self.xml)
        with codecs.open(out_fname, 'wb') as fout:
            fout.write(xml_str)
        return True


def main(args = None):
    DESCRIPTION=textwrap.dedent("""\
            The input file sem should contain the parsed sentences. All CCG trees correspond
            to the premises, except the last one, which is the hypothesis.
      """)

    parser = argparse.ArgumentParser(
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=DESCRIPTION)
    parser.add_argument('out', help='XML merged output filename')
    parser.add_argument('--input', action='append', nargs=2,
        metavar=('label', 'filename'),
        help='Merges the CCG and semantic trees from input filenames.')
    args = parser.parse_args()

    logging.basicConfig(level=logging.WARNING)

    for label, ifname in args.input:
        if not os.path.exists(ifname):
            print('File does not exist: {0}'.format(ifname), file=sys.stderr)
            parser.print_help(file=sys.stderr)
            sys.exit(1)

    parser = etree.XMLParser(remove_blank_text=True)

    merger = Merger()
    for label, ifname in args.input:
        root = etree.parse(ifname, parser)
        merger.add(root, label)

    merger.write(args.out)

if __name__ == '__main__':
    main()
