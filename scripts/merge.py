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
    for sem in root.xpath('./document/sentences/sentence/semantics'):
        sem.set('ccg_id', '{0}_{1}'.format(label, sem.get('ccg_id')))
    return root

def create_index(root):
    index = {doc.get('pair_id') : doc for doc in root.xpath('./document')}
    return index

def insert_nodes_by_tag(target, nodes, tag):
    assert isinstance(nodes, list)

class Merger(object):
    """
    Merges XML RTE problems according to their pair_id.
    """

    def __init__(self):
        self.id2doc = None
        self.root = None

    def add(self, root, label=None):
        root = relabel(root, label)
        if self.root is None:
            self.root = root
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
                assert len(orig_sents) == len(new_sents), '%d vs. %d' % len(orig_sents), len(new_sents)
                for orig_sent, new_sent in zip(orig_sents, new_sents):
                    new_ccgs = new_sent.xpath('./ccg')
                    if new_ccgs:
                        insert_nodes_by_tag(orig_sent, new_ccgs, 'ccg')
                    new_sems = new_sent.xpath('./semantics')
                    if new_sems:
                        insert_nodes_by_tag(orig_sent, new_sems, 'semantics')
        return


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

    root = None
    for label, ifname in args.input:
        lroot = etree.parse(ifname, parser)
        relabel(lroot, label)
        if root is None:
            root = lroot
        else:
            merge(lroot, root)

    sentences_orig = doc_orig.xpath('//sentence')

    root_xml_str = serialize_tree(root)
    with codecs.open(fname, 'wb') as fout:
        fout.write(root_xml_str)

if __name__ == '__main__':
    main()
