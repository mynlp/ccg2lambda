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

from semantic_tools import prove_doc
from visualization_tools import convert_doc_to_mathml
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
    parser.add_argument("--graph_out", nargs='?', type=str, default="",
        help="HTML graphical output filename.")
    # parser.add_argument("--abduction", action="store_true", default=False)
    parser.add_argument("--abduction", nargs='?', type=str, default="no",
        choices=["no", "naive", "spsa"],
        help="Activate on-demand axiom injection (default: no axiom injection).")
    parser.add_argument("--gold_trees", action="store_true", default=False)
    args = parser.parse_args()

    logging.basicConfig(level=logging.WARNING)
      
    if not os.path.exists(args.sem):
        print('File does not exist: {0}'.format(args.sem), file=sys.stderr)
        parser.print_help(file=sys.stderr)
        sys.exit(1)
    
    parser = etree.XMLParser(remove_blank_text=True)
    doc_orig = etree.parse(args.sem, parser)

    sentences_orig = doc_orig.xpath('//sentence')
    num_sentences = len(sentences_orig)

    res = etree.Element('root')
    for i in range(num_sentences // 2):
        doc = etree.Element('document')
        res.append(doc)
        doc.set('id', 'd' + str(i))
        sentences = etree.Element('sentences')
        doc.append(sentences)
        sentences.append(sentences_orig[i * 2])
        sentences.append(sentences_orig[i * 2 + 1])

    res_xml_str = serialize_tree(res)
    with codecs.open(args.rte, 'wb') as fout:
        fout.write(res_xml_str)

if __name__ == '__main__':
    main()
