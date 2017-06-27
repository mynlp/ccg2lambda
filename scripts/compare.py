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

def index_docs_by(rte_docs, attribute):
    attr_to_doc = {}
    for doc in rte_docs.xpath('//document'):
        attr_to_doc[doc.get(attribute, None)] = doc
    return attr_to_doc
    

def main(args = None):
    DESCRIPTION=textwrap.dedent("""\
            The XML input file proof should contain the gold and automatic inference results.
      """)

    parser = argparse.ArgumentParser(
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=DESCRIPTION)
    parser.add_argument("reference",
        help="XML reference with RTE results (<proof> nodes).")
    parser.add_argument("system",
        help="XML system RTE results (<proof> nodes).")
    args = parser.parse_args()

    logging.basicConfig(level=logging.WARNING)

    if not os.path.exists(args.reference):
        print('Reference XML file does not exist: {0}'.format(args.reference),
            file=sys.stderr)
        parser.print_help(file=sys.stderr)
        sys.exit(1)
    if not os.path.exists(args.system):
        print('System XML file does not exist: {0}'.format(args.system),
            file=sys.stderr)
        parser.print_help(file=sys.stderr)
        sys.exit(1)

    parser = etree.XMLParser(remove_blank_text=True)
    rte_docs_ref = etree.parse(args.reference, parser)
    rte_docs_sys = etree.parse(args.system, parser)

    print('Ref. docs: {0}, Sys. docs: {1}'.format(
        len(rte_docs_ref.xpath('//document')),
        len(rte_docs_sys.xpath('//document'))))

    ref_index = index_docs_by(rte_docs_ref, 'pair_id')
    sys_index = index_docs_by(rte_docs_sys, 'pair_id')

    # from pudb import set_trace; set_trace()
    pair_ids = sorted(set(ref_index.keys()).union(set(sys_index.keys())))
    for pair_id in pair_ids:
        ref_doc = ref_index.get(pair_id, None)
        sys_doc = sys_index.get(pair_id, None)
        if (ref_doc is None) ^ (sys_doc is None):
            print('{0}, Ref. doc: {1}, Sys. doc: {2}'.format(
                pair_id, ref_doc, sys_doc))
            continue
        ref_label = ref_doc.xpath('./proof/@inference_result')[0]
        sys_label = sys_doc.xpath('./proof/@inference_result')[0]
        if ref_label != sys_label:
            gold_label = ref_doc.xpath('./@rte_label')[0]
            print('{0}, Gold label: {1}, Ref. doc label: {2}, Sys. doc label: {3}'.format(
                pair_id.rjust(14), gold_label.rjust(7), ref_label.rjust(7), sys_label.rjust(7)))


if __name__ == '__main__':
    main()
