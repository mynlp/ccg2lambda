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

from tqdm import tqdm

from pandas_ml import ConfusionMatrix
from visualization_tools import convert_doc_to_mathml
from visualization_tools import wrap_mathml_in_html

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

possible_inference_results = set(['yes', 'no', 'unknown'])
def select_result(inference_results):
    """
    inference_results is a list with elements {'yes', 'no', 'unknown'}.
    """
    if not inference_results:
        return 'unknown'
    for r in inference_results:
        assert r in possible_inference_results, '{0} not in {1}'.format(r, possible_inference_results)
        if r != 'unknown':
            return r
    return 'unknown'

def get_sys_labels(roots):
    labels = dict()
    for root in roots:
        for doc in root.xpath('./document'):
            problem_id = doc.get('pair_id', None)
            if problem_id is not None and labels.get(problem_id, None) not in ['yes', 'no']:
                inference_results = doc.xpath('./proof/@inference_result')
                labels[problem_id] = select_result(inference_results)
    return labels
    
def get_gold_labels(roots):
    labels = dict()
    for root in roots:
        for doc in root.xpath('./document'):
            problem_id = doc.get('pair_id', None)
            rte_label = doc.get('rte_label', None)
            if problem_id is not None and rte_label is not None:
                if problem_id in labels and labels[problem_id] != rte_label:
                    logging.warning(
                        'problem_id {0} with different rte_label: {1} vs {2}'.format(
                        problem_id, labels[problem_id], rte_label))
                else:
                    labels[problem_id] = rte_label
    return labels

def print_accuracy(gold_labels, sys_labels):
    if len(gold_labels) != len(sys_labels):
        logging.warning(
            'In computing accuracy, the number of gold and system labels differs: g{0} vs s{1}.'.format(
            len(gold_labels), len(sys_labels)))
    hits = 0
    for prob_id, gold_label in gold_labels.items():
        if sys_labels.get(prob_id, 'unknown') == gold_label:
            hits += 1
    accuracy = float(hits) / len(gold_labels)
    print('Accuracy: {0:.4f} ({1}/{2})'.format(accuracy, hits, len(gold_labels)))

def print_label_distribution(labels, title=''):
    c = Counter(labels.values())
    print('Label Distribution {0}: {1}'.format(title.rjust(5), c))

def print_confusion_matrix(gold_id_labels, sys_id_labels):
    gold_ids = gold_id_labels.keys()
    gold_labels = [gold_id_labels[i] for i in gold_ids]
    sys_labels = [sys_id_labels.get(i, 'unknown') for i in gold_ids]
    c = ConfusionMatrix(gold_labels, sys_labels)
    print('Confusion matrix:\n{0}'.format(c))
    true_positives = c.get('yes', 'yes') + c.get('no', 'no')
    true_negatives = c.get('unknown', 'unknown')
    false_positives = c.get('unknown', 'yes') + c.get('unknown', 'no') + c.get('no', 'yes') + c.get('yes', 'no')
    false_negatives = c.get('yes', 'unknown') + c.get('no', 'unknown')
    print('Precision      : {0:.4f}'.format(
        float(true_positives) / (true_positives + false_positives)))
    print('Recall         : {0:.4f}'.format(
        float(true_positives) / (true_positives + false_negatives)))
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
        return [p for root in roots for p in root.xpath('./document')]
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

def make_html_header():
    return (
        "<!doctype html>\n"
        "<html lang='en'>\n"
        "<head>\n"
        "  <meta charset='UTF-8'>\n"
        "  <title>Evaluation results</title>\n"
        "  <style>\n"
        "    body {\n"
        "      font-size: 1.5em;\n"
        "    }\n"
        "  </style>\n"
        "</head>\n"
        "<body>\n"
        "<table border='1'>\n"
        "<tr>\n"
        "  <td>sick problem</td>\n"
        "  <td>gold answer</td>\n"
        "  <td>system answer</td>\n"
        "  <td>proving time</td>\n"
        "</tr>\n")

def make_html_tail():
    return '</table>\n</body>\n</html>'

def print_html_problem(doc, dir_name):
    prob_id = doc.get('pair_id', '00000')
    prob_html_fname = dir_name + '/' + prob_id + '.html'
    if prob_id == '00000':
        logging.warning(
            'RTE problem ID unspecified. Overwriting ' + prob_html_fname)
    coq_scripts = doc.xpath('./proof/theorems/theorem/coq_script/text()')
    mathml_str = convert_doc_to_mathml(doc)
    html_str = wrap_mathml_in_html(mathml_str)
    with codecs.open(prob_html_fname, 'w', 'utf-8') as fout:
        fout.write(html_str)
    return

red_color="rgb(255,0,0)"
green_color="rgb(0,255,0)"
white_color="rgb(255,255,255)"
gray_color="rgb(136,136,136)"
def print_html_problems(problems, fname_base, dir_name):
    html_head = make_html_header()
    with codecs.open('{0}/{1}.html'.format(dir_name, fname_base), 'w', 'utf-8') as fout:
        fout.write(html_head)
        for p in tqdm(problems):
            print_html_problem(p, dir_name)
            gold_label = p.get('rte_label', 'None')
            sys_label = p.xpath('./proof/@inference_result')[0]
            if gold_label == 'unknown' and sys_label != 'unknown':
                color = red_color # false positive
            elif gold_label == sys_label:
                color = green_color # true positive and true negative.
            elif gold_label != 'unknown' and sys_label == 'unknown':
                color = gray_color # false negative
            else:
                color = white_color
            prob_id = p.get('pair_id', '00000')
            prob_html_fname = prob_id + '.html'
            proving_time = -1.0
            html_str = (
                '<tr>\n'
                '  <td><a style="background-color:{0};" href="{1}">{2}</a></td>\n'
                '  <td>{3}</td>\n'
                '  <td>{4}</td>\n'
                '  <td>{5}s</td>\n'
                '</tr>\n').format(
                color, prob_html_fname, prob_id, gold_label, sys_label, proving_time)
            fout.write(html_str)
        html_tail = make_html_tail()
        fout.write(html_tail)

def print_html(roots, fname_base='main', dir_name='results'):
    print('Creating HTML graphical output. Please be patient...')
    problems = get_problems(roots, '')
    print_html_problems(problems, fname_base + '_all', dir_name)
    print('HTML graphical output written to {0}/{1}_all.html'.format(dir_name, fname_base))

def main(args = None):
    DESCRIPTION=textwrap.dedent("""\
            The XML input file proof should contain the gold and automatic inference results.
      """)

    parser = argparse.ArgumentParser(
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=DESCRIPTION)
    parser.add_argument("proofs", nargs='+',
        help="XML input filename(s) with proof results.")
    parser.add_argument("--dir_name", nargs='?', type=str, default='',
        help="Directory name where evaluation results will be stored.")
    args = parser.parse_args()

    logging.basicConfig(level=logging.WARNING)

    if any(not os.path.exists(p) for p in args.proofs):
        print('One of the files does not exists: {0}'.format(args.proofs),
            file=sys.stderr)
        parser.print_help(file=sys.stderr)
        sys.exit(1)

    proof_fnames = args.proofs

    roots = load_files(proof_fnames)
    gold_labels = get_gold_labels(roots)
    sys_labels = get_sys_labels(roots)
    print('Number of problems processed: {0}'.format(len(sys_labels)))

    if gold_labels:
        print_accuracy(gold_labels, sys_labels)
        print_confusion_matrix(gold_labels, sys_labels)
        print_label_distribution(gold_labels, 'gold')
        print_label_distribution(sys_labels, 'sys')

        print_stats_for(roots, 'false_positives')
        print_stats_for(roots, 'false_negatives')
        print_stats_for(roots, 'true_positives')
        print_stats_for(roots, 'true_negatives')
    else:
        logging.warning('No gold RTE labels provided.')

    print_num_syntactic_errors(roots)
    print_num_semantic_errors(roots)
    print_proof_status_stats(roots)

    if args.dir_name:
        if not os.path.exists(args.dir_name):
            os.makedirs(args.dir_name)
        print_html(roots, 'main', args.dir_name)

    # fps = get_problems(roots, 'false_negatives')
    # for fp in fps:
    #     print('{0} {1} {2}'.format(
    #         fp.get('pair_id'),
    #         fp.get('rte_label'),
    #         fp.xpath('./proof/@inference_result')[0]))

if __name__ == '__main__':
    main()
