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
import fileinput
import logging
import json
import os
import sys
import textwrap

from pycorenlp import StanfordCoreNLP

from semparse import serialize_tree

# Requires to previously run Stanford 3.6.0 server from its own directory:
# java -mx4g -cp "*" edu.stanford.nlp.pipeline.StanfordCoreNLPServer -port 9000 -timeout 15000
nlp = StanfordCoreNLP('http://localhost:9000')
def parse_sentence_const(sentence):
    """
    Parses the lowercased sentence into a constituent tree,
    returned as a string.
    Usage:
      >> print(parse_sentence_const('this is a test.'))
      (ROOT (S (NP (DT this)) (VP (VBZ is) (NP (DT a) (NN test))) (. .)))
    """
    res = nlp.annotate(sentence, properties={
        'annotators' : 'tokenize,ssplit,truecase,pos,parse',
        'outputFormat' : 'json'})
    tree_str = res['sentences'][0]['parse']
    tree_str = ' '.join(c.strip() for c in tree_str.split('\n'))
    return tree_str

def main(args = None):
    DESCRIPTION=textwrap.dedent("""\
            Transform the SICK dataset into the jsonl SNLI format.
      """)

    parser = argparse.ArgumentParser(
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=DESCRIPTION)
    # parser.add_argument("sick", help="TXT input filename with SICK SemEval problems.")
    args = parser.parse_args()

    logging.basicConfig(level=logging.WARNING)
      
    # if not os.path.exists(args.sick):
    #     print('File does not exist: {0}'.format(args.sick), file=sys.stderr)
    #     parser.print_help(file=sys.stderr)
    #     sys.exit(1)

    for sick_line in fileinput.input():
        if sick_line.startswith('pair_ID'):
            continue
        fields = [f.strip() for f in sick_line.strip().split('\t')]
        assert 6 == len(fields), fields
        pair_id, t, h, similarity, judgement, dset = fields
        judgement, dset = judgement.lower(), dset.lower()
        t_parse = parse_sentence_const(t)
        h_parse = parse_sentence_const(h)
        problem = {
            'gold_label': judgement,
            'sentence1': t,
            'sentence2': h,
            'sentence1_parse': t_parse,
            'sentence2_parse': h_parse,
            'similarity': similarity,
            'set': dset,
            'pairID': pair_id}
        print(json.dumps(problem))


if __name__ == '__main__':
    main()

