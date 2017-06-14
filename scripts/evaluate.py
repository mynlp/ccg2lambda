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

def print_evaluation(gold_labels, sys_labels):
    hits = sum(int(g == s) for g, s in zip(gold_labels, sys_labels))
    accuracy = float(hits) / len(sys_labels)
    print('Accuracy: {0:.2f}'.format(accuracy))

def main(args = None):
    DESCRIPTION=textwrap.dedent("""\
            The XML input file proof should contain the gold and automatic inference results.
      """)

    parser = argparse.ArgumentParser(
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=DESCRIPTION)
    parser.add_argument("proofs", nargs='+',
        help="XML input filename(s) with proof results.")
    args = parser.parse_args()

    logging.basicConfig(level=logging.WARNING)
      
    if any(not os.path.exists(p) for p in args.proofs):
        print('One of the files does not exists: {0}'.format(args.proofs),
            file=sys.stderr)
        parser.print_help(file=sys.stderr)
        sys.exit(1)

    parser = etree.XMLParser(remove_blank_text=True)
    gold_labels = []
    sys_labels = []
    for fname in args.proofs:
        rte_docs = etree.parse(fname, parser)
        gold_labels.extend(rte_docs.xpath('//document/@rte_label'))
        sys_labels.extend(rte_docs.xpath('//document/proof/@inference_result'))
    assert len(gold_labels) == len(sys_labels), \
        '{0} != {1}'.format(len(gold_labels) == len(sys_labels))

    print_evaluation(gold_labels, sys_labels)


if __name__ == '__main__':
    main()
