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

from collections import OrderedDict
import json
import logging
import re
from subprocess import Popen
import subprocess
import sys

from nltk import Tree

from coq_analyzer import get_predicate_arguments
from knowledge import get_lexical_relations_from_preds
from normalization import denormalize_token
from theorem import is_theorem_defined
from theorem import is_theorem_error
from theorem import run_coq_script
from theorem import insert_axioms_in_coq_script
from tactics import get_tactics
from tree_tools import tree_or_string, tree_contains

def find_final_subgoal_line_index_(coq_output_lines):
    indices = [i for i, line in enumerate(coq_output_lines)
               if line.endswith('subgoal')]
    if not indices:
        return None
    return indices[-1]


def find_final_conclusion_sep_line_index_(coq_output_lines):
    indices = [i for i, line in enumerate(coq_output_lines)
               if line.startswith('===') and line.endswith('===')]
    if not indices:
        return None
    return indices[-1]


def get_premise_lines_(coq_output_lines):
    premise_lines = []
    line_index_last_conclusion_sep = find_final_conclusion_sep_line_index(
        coq_output_lines)
    if not line_index_last_conclusion_sep:
        return premise_lines
    for line in coq_output_lines[line_index_last_conclusion_sep - 1:0:-1]:
        if line == "":
            return premise_lines
        else:
            premise_lines.append(line)
    return premise_lines


def get_conclusion_line_(coq_output_lines):
    line_index_last_conclusion_sep = find_final_conclusion_sep_line_index(
        coq_output_lines)
    if not line_index_last_conclusion_sep:
        return None
    return coq_output_lines[line_index_last_conclusion_sep + 1]

def get_premises_that_match_conclusion_args_(premises, conclusion):
    """
    Returns premises where the predicates have at least one argument
    in common with the conclusion.
    This function was used for EACL 2017.
    """
    conclusion_terms = [c.strip(')(') for c in conclusion.split()]
    conclusion_args = set(conclusion_terms[1:])
    candidate_premises = []
    for premise in premises:
        premise_terms = [p.strip(')(') for p in premise.split()[2:]]
        premise_args = set(premise_terms[1:])
        logging.debug('Conclusion args: ' + str(conclusion_args) +
                      '\nPremise args: ' + str(premise_args))
        if premise_args.intersection(conclusion_args):
            candidate_premises.append(premise)
    return candidate_premises


def get_premises_that_match_conclusion_args_(premises, conclusion):
    """
    Returns premises where the predicates have at least one argument
    in common with the conclusion.
    """
    candidate_premises = []
    conclusion = re.sub(r'\?([0-9]+)', r'?x\1', conclusion)
    conclusion_args = get_tree_pred_args(conclusion, is_conclusion=True)
    if conclusion_args is None:
        return candidate_premises
    for premise_line in premises:
        # Convert anonymous variables of the form ?345 into ?x345.
        premise_line = re.sub(r'\?([0-9]+)', r'?x\1', premise_line)
        premise_args = get_tree_pred_args(premise_line)
        logging.debug('Conclusion args: ' + str(conclusion_args) +
                      '\nPremise args: ' + str(premise_args))
        if tree_contains(premise_args, conclusion_args):
            candidate_premises.append(premise_line)
    return candidate_premises


def make_failure_log_(conclusion_pred, premise_preds, conclusion, premises,
                     coq_output_lines=None):
    """
    Produces a dictionary with the following structure:
    {"unproved sub-goal" : "sub-goal_predicate",
     "matching premises" : ["premise1", "premise2", ...],
     "raw sub-goal" : "conclusion",
     "raw premises" : ["raw premise1", "raw premise2", ...]}
    Raw sub-goal and raw premises are the coq lines with the premise
    internal name and its predicates. E.g.
    H : premise (Acc x1)
    Note that this function is not capable of returning all unproved
    sub-goals in coq's stack. We only return the top unproved sub-goal.
    """
    failure_log = OrderedDict()
    conclusion_base = denormalize_token(conclusion_pred)
    # failure_log["unproved sub-goal"] = conclusion_base
    premises_base = [denormalize_token(p) for p in premise_preds]
    # failure_log["matching premises"] = premises_base
    # failure_log["raw sub-goal"] = conclusion
    # failure_log["raw premises"] = premises
    premise_preds = []
    for p in premises:
        try:
            pred = p.split()[2]
        except:
            continue
        if pred.startswith('_'):
            premise_preds.append(denormalize_token(pred))
    failure_log["all_premises"] = premise_preds
    failure_log["other_sub-goals"] = get_subgoals_from_coq_output(
        coq_output_lines, premises)
    failure_log["other_sub-goals"].insert(0, {
        'subgoal': conclusion_base,
        'index': 1,
        'raw_subgoal': conclusion,
        'matching_premises' : premises_base,
        'matching_raw_premises' : premises_base})
    failure_log["type_error"] = has_type_error(coq_output_lines)
    failure_log["open_formula"] = has_open_formula(coq_output_lines)
    return failure_log


def has_type_error_(coq_output_lines):
    for line in coq_output_lines:
        if 'has type' in line and 'while it is expected to have type' in line:
            return 'yes'
    return 'no'


def has_open_formula_(coq_output_lines):
    for line in coq_output_lines:
        if 'The type of this term is a product while it is expected to be' in line:
            return 'yes'
        if '(fun F' in line:
            return 'yes'
    return 'no'


def get_subgoals_from_coq_output_(coq_output_lines, premises):
    """
    When the proving is halted due to unprovable sub-goals,
    Coq produces an output similar to this:

    2 subgoals

      H1 : True
      H4 : True
      x1 : Event
      H6 : True
      H3 : _play x1
      H : _two (Subj x1)
      H2 : _man (Subj x1)
      H0 : _table (Acc x1)
      H5 : _tennis (Acc x1)
      ============================
       _ping (Acc x1)

    subgoal 2 is:
      _pong (Acc x1)

    This function returns the remaining sub-goals ("_pong" in this example).
    """
    subgoals = []
    subgoal_index = -1
    for line in coq_output_lines:
        if line.strip() == '':
            continue
        line_tokens = line.split()
        if subgoal_index > 0:
            subgoal_line = line
            subgoal_tokens = subgoal_line.split()
            subgoal_pred = subgoal_tokens[0]
            if subgoal_index in [s['index'] for s in subgoals]:
                # This sub-goal has already appeared and is recorded.
                subgoal_index = -1
                continue
            subgoal = {
                'subgoal': denormalize_token(line_tokens[0]),
                'index': subgoal_index,
                'raw_subgoal': subgoal_line}
            matching_premises = get_premises_that_match_conclusion_args(
                premises, subgoal_line)
            subgoal['matching_raw_premises'] = matching_premises
            premise_preds = [
                denormalize_token(premise.split()[2]) for premise in matching_premises]
            subgoal['matching_premises'] = premise_preds
            subgoals.append(subgoal)
            subgoal_index = -1
        if len(line_tokens) >= 3 and line_tokens[0] == 'subgoal' and line_tokens[2] == 'is:':
            subgoal_index = int(line_tokens[1])
    return subgoals


def make_axioms_from_premises_and_conclusion(premises, conclusion, coq_output_lines=None):
    matching_premises = get_premises_that_match_conclusion_args(
        premises, conclusion)
    premise_preds = [premise.split()[2] for premise in matching_premises]
    conclusion_pred = conclusion.split()[0]
    pred_args = get_predicate_arguments(premises, conclusion)
    axioms = make_axioms_from_preds(premise_preds, conclusion_pred, pred_args)
    # print('Has axioms: {0}'.format(axioms), file=sys.stderr)
    failure_log = OrderedDict()
    if not axioms:
        failure_log = make_failure_log(
            conclusion_pred, premise_preds, conclusion, premises, coq_output_lines)
        # print(json.dumps(failure_log), file=sys.stderr)
    return axioms, failure_log


def parse_coq_line_(coq_line):
    try:
        tree_args = tree_or_string('(' + coq_line + ')')
    except ValueError:
        tree_args = None
    return tree_args


def get_tree_pred_args_(line, is_conclusion=False):
    """
    Given the string representation of a premise, where each premise is:
      pX : predicate1 (arg1 arg2 arg3)
      pY : predicate2 arg1
    or the conclusion, which is of the form:
      predicate3 (arg2 arg4)
    returns a tree or a string with the arguments of the predicate.
    """
    tree_args = None
    if not is_conclusion:
        tree_args = parse_coq_line(' '.join(line.split()[2:]))
    else:
        tree_args = parse_coq_line(line)
    if tree_args is None or len(tree_args) < 1:
        return None
    return tree_args[0]


def get_predicate_arguments_(premises, conclusion):
    """
    Given the string representations of the premises, where each premises is:
      pX : predicate1 arg1 arg2 arg3
    and the conclusion, which is of the form:
      predicate3 arg2 arg4
    returns a dictionary where the key is a predicate, and the value
    is a list of argument names.
    If the same predicate is found with different arguments, then it is
    labeled as a conflicting predicate and removed from the output.
    Conflicting predicates are typically higher-order predicates, such
    as "Prog".
    """
    pred_args = {}
    pred_trees = []
    for premise in premises:
        try:
            pred_trees.append(
                Tree.fromstring('(' + ' '.join(premise.split()[2:]) + ')'))
        except ValueError:
            continue
    try:
        conclusion_tree = Tree.fromstring('(' + conclusion + ')')
    except ValueError:
        return pred_args
    pred_trees.append(conclusion_tree)

    pred_args_list = []
    for t in pred_trees:
        pred = t.label()
        args = t.leaves()
        pred_args_list.append([pred] + args)
    conflicting_predicates = set()
    for pa in pred_args_list:
        pred = pa[0]
        args = pa[1:]
        if pred in pred_args and pred_args[pred] != args:
            conflicting_predicates.add(pred)
        pred_args[pred] = args
    logging.debug('Conflicting predicates: ' + str(conflicting_predicates))
    for conf_pred in conflicting_predicates:
        del pred_args[conf_pred]
    return pred_args


def make_axioms_from_preds(premise_preds, conclusion_pred, pred_args):
    axioms = set()
    linguistic_axioms = \
        get_lexical_relations_from_preds(
            premise_preds, conclusion_pred, pred_args)
    axioms.update(set(linguistic_axioms))
    # if not axioms:
    #   approx_axioms = GetApproxRelationsFromPreds(premise_preds, conclusion_pred)
    #   axioms.update(approx_axioms)
    return axioms


def try_abductions(theorem):
    assert len(theorem.variations) == 2, 'Got %d variations' % len(theorem.variations)
    theorem_master = theorem.variations[0]
    theorem_negated = theorem.variations[1]
    t_pos, t_neg = theorem_master, theorem_negated

    direct_proof_script = t_pos.coq_script
    reverse_proof_script = t_neg.coq_script
    axioms = t_pos.axioms.union(t_neg.axioms)
    current_axioms = t_pos.axioms.union(t_neg.axioms)
    failure_logs = []
    while True:
        # inference_result_str, direct_proof_scripts, new_direct_axioms, failure_log = \
        abduction_theorem = try_abduction(
            t_pos, previous_axioms=current_axioms, expected='yes')
        current_axioms = axioms.union(abduction_theorem.axioms)
        reverse_proof_scripts = []
        if theorem_master.result == 'unknown':
            abduction_theorem = try_abduction(
                t_neg, previous_axioms=current_axioms, expected='no')
            theorem_master.variations.append(abduction_theorem)
            current_axioms.update(abduction_theorem.axioms)
        if len(axioms) == len(current_axioms) or theorem_master.result != 'unknown':
            break
        axioms = {a for a in current_axioms}
    return

def try_abductions_(theorem):
    assert len(theorem.variations) == 2, 'Got %d variations' % len(theorem.variations)
    theorem_master = theorem.variations[0]
    theorem_negated = theorem.variations[1]
    t_pos, t_neg = theorem_master, theorem_negated

    direct_proof_script = t_pos.coq_script
    reverse_proof_script = t_neg.coq_script
    axioms = t_pos.axioms.union(t_neg.axioms)
    current_axioms = t_pos.axioms.union(t_neg.axioms)
    failure_logs = []
    while True:
        # inference_result_str, direct_proof_scripts, new_direct_axioms, failure_log = \
        abduction_theorem = try_abduction(
            t_pos, previous_axioms=current_axioms, expected='yes')
        if len(t_pos.axioms) < len(new_direct_axioms):
            new_theorem = t_pos.copy(new_axioms=new_direct_axioms)
            new_theorem.coq_script = direct_proof_scripts[-1]
            new_theorem.failure_log = failure_log
            new_theorem.inference_result = True if inference_result_str == 'yes' else False
        current_axioms = axioms.union(new_direct_axioms)
        reverse_proof_scripts = []
        if not inference_result_str == 'yes':
            inference_result_str, reverse_proof_scripts, new_reverse_axioms, failure_log = \
                try_abduction(t_neg,
                              previous_axioms=current_axioms, expected='no')
            if len(t_neg.axioms) < len(new_reverse_axioms):
                new_theorem = t_neg.copy(new_axioms=new_reverse_axioms)
                new_theorem.coq_script = reverse_proof_scripts[-1]
                new_theorem.failure_log = failure_log
                new_theorem.inference_result = True if inference_result_str == 'no' else False
                t_pos.variations.append(new_theorem)
            current_axioms.update(new_reverse_axioms)
        if len(axioms) == len(current_axioms) or inference_result_str != 'unknown':
            break
        axioms = {a for a in current_axioms}
    return

def try_abductions_(coq_scripts):
    assert len(coq_scripts) == 2
    direct_proof_script = coq_scripts[0]
    reverse_proof_script = coq_scripts[1]
    axioms = set()
    failure_logs = []
    while True:
        inference_result_str, direct_proof_scripts, new_direct_axioms, failure_log = \
            try_abduction(direct_proof_script,
                          previous_axioms=axioms, expected='yes')
        current_axioms = axioms.union(new_direct_axioms)
        failure_logs.append(failure_log)
        reverse_proof_scripts = []
        if not inference_result_str == 'yes':
            inference_result_str, reverse_proof_scripts, new_reverse_axioms, failure_log = \
                try_abduction(reverse_proof_script,
                              previous_axioms=current_axioms, expected='no')
            current_axioms.update(new_reverse_axioms)
            failure_logs.append(failure_log)
        all_scripts = direct_proof_scripts + reverse_proof_scripts
        if len(axioms) == len(current_axioms) or inference_result_str != 'unknown':
            break
        axioms = current_axioms
    return inference_result_str, all_scripts, failure_logs


def filter_wrong_axioms(axioms, coq_script):
    good_axioms = set()
    for axiom in axioms:
        new_coq_script = insert_axioms_in_coq_script(set([axiom]), coq_script)
        # We only need to check if there is a type mismatch, which should
        # be fast (2 secs. maximum).
        output_lines = run_coq_script(new_coq_script, timeout=2)
        if not is_theorem_error(output_lines):
            good_axioms.add(axiom)
    return good_axioms


def try_abduction_(theorem, previous_axioms=None, expected='yes'):
    if previous_axioms is None:
        previous_axioms = set()
    coq_script = theorem.coq_script
    inference_result, failure_log = theorem.prove_debug(previous_axioms)
    if inference_result:
        abduction_theorem = theorem.copy(new_axioms=previous_axioms)
        return abduction_theorem

    axioms, failure_log = make_axioms_from_premises_and_conclusion(
        premise_lines, conclusion, output_lines)
    axioms = filter_wrong_axioms(axioms, coq_script)
    axioms = axioms.union(previous_axioms)
    new_coq_script = insert_axioms_in_coq_script(axioms, coq_script)
    output_lines = run_coq_script(new_coq_script, timeout=100)
    inference_result_str = expected if is_theorem_defined(output_lines) else 'unknown'
    return inference_result_str, [new_coq_script], axioms, failure_log

def make_axioms_from_coq_analysis(failure_log):
    axioms = set()
    for subgoal in failure_log.get('other_sub-goals', []):
        conclusion_pred = subgoal.get('subgoal', '')
        premise_preds = subgoal.get('matching_premises', [])
        pred_args = get_predicate_arguments(
            subgoal.get('matching_raw_premises', []),
            subgoal.get('raw_subgoal', ''))
        subgoal_axioms = make_axioms_from_preds(
            premise_preds, conclusion_pred, pred_args)
        axioms.update(subgoal_axioms)
    return axioms

def try_abduction(theorem, previous_axioms=None, expected='yes'):
    if previous_axioms is None:
        previous_axioms = set()
    inference_result, failure_log = theorem.prove_debug(previous_axioms)
    if inference_result is True:
        abduction_theorem = theorem.copy(new_axioms=previous_axioms)
        return abduction_theorem

    axioms = make_axioms_from_coq_analysis(failure_log)
    axioms = filter_wrong_axioms(axioms, theorem.coq_script)
    axioms = axioms.union(previous_axioms)
    abduction_theorem = theorem.copy(new_axioms=axioms)
    abduction_theorem.prove_simple()
    return abduction_theorem

