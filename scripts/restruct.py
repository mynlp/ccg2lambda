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
import json
from lxml import etree
import os
import sys
import textwrap

from semparse import serialize_tree

def main(args = None):
    DESCRIPTION=textwrap.dedent("""\
            The input file sem should contain the parsed sentences. All CCG trees correspond
            to the premises, except the last one, which is the hypothesis.
      """)

    parser = argparse.ArgumentParser(
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=DESCRIPTION)
    parser.add_argument("sem", help="XML input filename with semantics")
    parser.add_argument("rte", help="XML input filename with RTE problems.")
    parser.add_argument("--doc_labels", default="",
        help="RTE labels (e.g. entailment judgment)")
    parser.add_argument("--split", nargs='?', type=int, default="-1",
        help="Number of RTE problems per XML file.")
    args = parser.parse_args()

    logging.basicConfig(level=logging.WARNING)
      
    if not os.path.exists(args.sem):
        print('File does not exist: {0}'.format(args.sem), file=sys.stderr)
        parser.print_help(file=sys.stderr)
        sys.exit(1)

    labels = []
    if args.doc_labels != "":
        if os.path.exists(args.doc_labels):
            with codecs.open(args.doc_labels, 'r', 'utf-8') as fin:
                for line in fin:
                    try:
                        l = json.loads(line.strip())
                    except ValueError:
                        l = {'label' : line.strip()}
                    labels.append(l)
        else:
            print('File does not exist: {0}. Ignoring labels.'.format(
                args.doc_labels), file=sys.stderr)

    parser = etree.XMLParser(remove_blank_text=True)
    doc_orig = etree.parse(args.sem, parser)

    sentences_orig = doc_orig.xpath('//sentence')
    num_sentences = len(sentences_orig)

    if labels:
        assert num_sentences // 2 == len(labels), \
            'Num RTE problems and labels mismatch: {0} vs. {1}'.format(
                num_sentences // 2, len(labels))

    num_docs = args.split if args.split > 0 else int(1e10)
    res = etree.Element('root')
    remaining_docs = False
    for i in range(num_sentences // 2):
        doc = etree.Element('document')
        res.append(doc)
        doc.set('id', 'd' + str(i))
        if labels:
            for name, value in labels[i].items():
                doc.set(name, value)
        sentences = etree.Element('sentences')
        doc.append(sentences)
        sentences.append(sentences_orig[i * 2])
        sentences.append(sentences_orig[i * 2 + 1])
        remaining_docs = True
        if i + 1 % num_docs == 0:
            save_xml_root(res, args.rte, i)
            remaining_docs = False
            res = etree.Element('root')
    if remaining_docs:
        save_xml_root(res, args.rte, num_sentences // 2)

def save_xml_root(root, fname, ind):
    # if fname.endswith('.xml'):
    #     fname = '{0}.{1}.xml'.format(fname[:-4], ind)
    root_xml_str = serialize_tree(root)
    with codecs.open(fname, 'wb') as fout:
        fout.write(root_xml_str)

if __name__ == '__main__':
    main()
