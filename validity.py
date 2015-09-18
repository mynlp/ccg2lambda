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

import logging
from lxml import etree
import os
import sys
import textwrap

from ccg2lambda_tools import assign_semantics_to_ccg
from semantic_index import SemanticIndex
from semantic_tools import prove_from_ccg
from visualization_tools import convert_trees_to_mathml

def main(args = None):
    USAGE=textwrap.dedent("""\
        Usage:
            python validity.py <categories_template.yaml> <parsed_sentences.xml> --[arbi-types|auto-types]

            categories_template.yaml should contain the semantic templates
              in YAML format.
            parsed_sentence.xml contains the parsed sentences. All CCG trees correspond
            to the premises, except the last one, which is the hypothesis.
            If --arbi-types flag is specified, then the arbitrary specification of
            coq_types is enabled. Thus, semantic rule assignments should contain a
            a field such as:
            - semantics: \P x.P(x)
              category: NP
              coq_type: Animal
            If --auto-types is enabled, or no flag is specified, then the automatic
            inference of types is enabled. This automatic inference relies on the naive
            implementation in the sem/logic module of NLTK.
      """)
    if args is None:
        args = sys.argv[1:]
    if len(args) not in [2, 3]:
        print('Wrong number of arguments.')
        print(USAGE)
        sys.exit(1)
    if not os.path.exists(args[0]) or not os.path.exists(args[1]):
        print('File does not exist: {0} or {1}'.format(args[0], args[1]))
        sys.exit(1)
    expression_templates_filename = args[0]
    parsed_sentences_filename = args[1]
    if len(args) == 3 and args[2] == '--arbi-types':
        arbi_types_requested = True
    else:
        arbi_types_requested = False

    logging.basicConfig(level=logging.WARNING)

    semantic_index = SemanticIndex(expression_templates_filename)

    ccg_xml_trees = etree.parse(parsed_sentences_filename).findall('.//sentence')

    logical_interpretations = []
    ccg_tree_list = []
    ccg_tokens_list = []
    for ccg_xml in ccg_xml_trees:
        ccg_tree = assign_semantics_to_ccg(ccg_xml, semantic_index)
        ccg_tree_list.append(ccg_tree)
        assert 'sem' in ccg_tree.attrib, \
          'The assignment of semantics to CCG tree may have failed. Tree: {0}'\
          .format(etree.tostring(ccg_tree, pretty_print=True, encoding = 'utf-8')\
                  .decode('utf-8'))
        lambda_expression = ccg_tree.get('sem')
        logical_interpretations.append(lambda_expression)
        ccg_tokens = ccg_xml.find("tokens")
        ccg_tokens_list.append(ccg_tokens)
    if arbi_types_requested:
        inference_result, coq_scripts = \
          prove_from_ccg(logical_interpretations, ccg_trees=ccg_tree_list,
                                                ccg_xml_trees=ccg_xml_trees)
    else:
        inference_result, coq_scripts = \
          prove_from_ccg(logical_interpretations, ccg_xml_trees=ccg_xml_trees)
    print(inference_result, file=sys.stdout)
    html_str = convert_trees_to_mathml(ccg_tree_list, ccg_tokens_list, coq_scripts)
    print(html_str, file=sys.stderr)

if __name__ == '__main__':
    main()
