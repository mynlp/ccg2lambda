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
from collections import Counter
import logging
from lxml import etree
import os
import sys
import textwrap

from pandas_ml import ConfusionMatrix

def load_files(proof_fnames):
    """
    From a list of XML filenames that contain a <proof> node,
    it returns a list of lxml root nodes.
    """
    roots = []
    parser = etree.XMLParser(remove_blank_text=True)
    for fname in proof_fnames:
        docs = etree.parse(fname, parser)
        roots.append(docs)
    return roots

def get_sys_labels(roots):
    labels = []
    for root in roots:
        labels.extend(root.xpath('./document/proof/@inference_result'))
    return labels
    
def get_gold_labels(roots):
    labels = []
    for root in roots:
        labels.extend(root.xpath('./document/@rte_label'))
    return labels

def print_accuracy(gold_labels, sys_labels):
    hits = sum(int(g == s) for g, s in zip(gold_labels, sys_labels))
    accuracy = float(hits) / len(sys_labels)
    print('Accuracy: {0:.2f}'.format(accuracy))

def print_label_distribution(labels, title=''):
    c = Counter(labels)
    print('Label Distribution {0}: {1}'.format(title.rjust(5), c))

def print_confusion_matrix(gold_labels, sys_labels):
    c = ConfusionMatrix(gold_labels, sys_labels)
    print('Confusion matrix:\n{0}'.format(c))
    true_positives = c.get('yes', 'yes') + c.get('no', 'no')
    true_negatives = c.get('unknown', 'unknown')
    false_positives = c.get('unknown', 'yes') + c.get('unknown', 'no')
    false_negatives = c.get('yes', 'unknown') + c.get('no', 'unknown')
    print('True positives : {0}'.format(true_positives))
    print('True negatives : {0}'.format(true_negatives))
    print('False positives: {0}'.format(false_positives))
    print('False negatives: {0}'.format(false_negatives))

def print_num_syntactic_errors(roots):
    """
    Syntactic parse errors are likely to be signaled by sentence XML nodes
    for which there is no 'tokens' node (failure of syntactic parser
    earlier in the pipeline).
    """
    syn_errors = [s for root in roots for s in root.xpath(
        './document/sentences/sentence') if not s.xpath('./tokens')]
    print('Syntactic parse errors: {0}'.format(len(syn_errors)))

def print_num_semantic_errors(roots):
    sem_errors = [se for root in roots for se in root.xpath(
        './document/sentences/sentence/semantics[@status="failed"]')]
    sem_syn_errors = [se for se in sem_errors if not se.getparent().xpath('./tokens')]
    print('Semantic parse errors: {0} (from which {1} are syntactic errors)'.format(
        len(sem_errors), len(sem_syn_errors)))

def print_proof_status_stats(roots):
    statuses = [s for root in roots for s in root.xpath('./document/proof/@status')]
    c = Counter(statuses)
    print('Proof status distribution: {0}'.format(c))

def get_problems(roots, error='false_positives'):
    if error == 'false_positives':
        cond = '@rte_label = "unknown" and ./proof/@inference_result != "unknown"'
    elif error == 'false_negatives':
        cond = '@rte_label != "unknown" and ./proof/@inference_result = "unknown"'
    elif error == 'true_positives':
        cond = '@rte_label != "unknown" and ./proof/@inference_result = @rte_label'
    elif error == 'true_negatives':
        cond = '@rte_label = "unknown" and ./proof/@inference_result = @rte_label'
    else:
        raise ValueError('Error type not recognized: {0}'.format(error))
    problems = [p for root in roots for p in root.xpath('./document[{0}]'.format(cond))]
    return problems

def get_open_formula(doc):
    f = doc.xpath('./proof/theorems/theorem/failure_log[1]/@open_formula')
    if len(f) == 0:
        return 'no'
    return f[0]

def get_type_error(doc):
    f = doc.xpath('./proof/theorems/theorem/failure_log[1]/@type_error')
    if len(f) == 0:
        return 'no'
    return f[0]

def print_stats_for(roots, error='false_positives'):
    problems = get_problems(roots, error)
    open_formulas = [get_open_formula(p) for p in problems]
    type_errors = [get_type_error(p) for p in problems]
    print('{0}: {1}'.format(error, len(problems)))
    ct = Counter(type_errors)
    print('  Type error distribution: {0}'.format(ct))
    co = Counter(open_formulas)
    print('  Open formula distribution: {0}'.format(co))

def print_evaluation(proof_fnames):
    roots = load_files(proof_fnames)
    gold_labels = get_gold_labels(roots)
    sys_labels = get_sys_labels(roots)
    assert len(gold_labels) == len(sys_labels), \
        '{0} != {1}'.format(len(gold_labels) == len(sys_labels))
    print('Number of problems: {0}'.format(len(gold_labels)))

    print_accuracy(gold_labels, sys_labels)
    print_confusion_matrix(gold_labels, sys_labels)
    print_label_distribution(gold_labels, 'gold')
    print_label_distribution(sys_labels, 'sys')

    print_num_syntactic_errors(roots)
    print_num_semantic_errors(roots)
    print_proof_status_stats(roots)

    print_stats_for(roots, 'false_positives')
    print_stats_for(roots, 'false_negatives')
    print_stats_for(roots, 'true_positives')
    print_stats_for(roots, 'true_negatives')

    # TODO: show errors, HTML, etc.


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

    proof_fnames = args.proofs
    print_evaluation(proof_fnames)


if __name__ == '__main__':
    main()
