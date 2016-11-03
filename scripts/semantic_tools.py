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

import codecs
import logging
import re
import simplejson
import string
import subprocess

from nltk import Tree
from nltk.sem.logic import (typecheck, read_type, ConstantExpression,
  AbstractVariableExpression, InconsistentTypeHierarchyException)

from knowledge import get_lexical_relations, get_tokens_from_ccg_tree
from logic_parser import lexpr
from nltk2coq import normalize_interpretation
from semantic_types import get_dynamic_library_from_doc

def build_knowledge_axioms(ccg_trees):
    return ''
    if ccg_trees is None:
        return ''
    axioms = get_lexical_relations(ccg_trees)
    axioms_str = ""
    for axiom in axioms:
        axioms_str += axiom + '\n'
        axiom_name = axiom.split()[1]
        axioms_str += 'Hint Resolve {0}.\n'.format(axiom_name)
    axioms_str += '\n'
    return axioms_str

def prove_from_ccg(logical_interpretations, ccg_trees = None, ccg_xml_trees = None):
    best_interpretations = \
      [str(interpretation) for interpretation in logical_interpretations]
    best_interpretations = \
      [resolve_prefix_to_infix_operations(interp) for interp in best_interpretations]
    premise_interpretations = best_interpretations[0:-1]
    conclusion = best_interpretations[-1]
    if ccg_trees != None:
        dynamic_library_coq = build_arbitrary_dynamic_library(ccg_trees)
        nltk_sig = convert_coq_signatures_to_nltk(dynamic_library_coq)
        dynamic_library_nltk = build_dynamic_library(logical_interpretations, nltk_sig)
        dynamic_library = merge_dynamic_libraries(
          coq_lib=dynamic_library_coq,
          nltk_lib=dynamic_library_nltk,
          coq_static_lib_path='coqlib.v', # Useful to get reserved predicates.
          ccg_xml_trees=ccg_xml_trees) # Useful to get full list of tokens for which we need to specify types.
    else:
        dynamic_library = build_dynamic_library(logical_interpretations)
    dynamic_library_str = '\n'.join(dynamic_library)
    knowledge_axioms = build_knowledge_axioms(ccg_xml_trees)
    dynamic_library_str += '\n\n' + knowledge_axioms
    coq_scripts = []
    inference_result, coq_script = \
      prove_statements(premise_interpretations, conclusion, dynamic_library_str)
    coq_scripts.append(coq_script)
    if inference_result:
        inference_result_str = 'yes'
    else:
        negated_conclusion = negate_conclusion(conclusion)
        inference_result, coq_script = \
          prove_statements(premise_interpretations, negated_conclusion, dynamic_library_str)
        coq_scripts.append(coq_script)
        if inference_result:
            inference_result_str = 'no'
        else:
            inference_result_str = 'unknown'
    return inference_result_str, coq_scripts

def get_formulas_from_doc(doc):
    """
    Returns string representations of logical formulas,
    as stored in the "sem" attribute of the root node
    of semantic trees.
    If a premise has no semantic representation, it is ignored.
    If there are no semantic representation at all, or the conclusion
    has no semantic representation, it returns None to signal an error.
    """
    formulas = [s.get('sem', None) for s in doc.xpath('//sentence/semantics/span[1]')]
    if len(formulas) < 2 or formulas[-1] == None:
        return None
    formulas = [f for f in formulas if f is not None]
    return formulas

def prove_doc(doc):
    """
    Retrieve from trees the logical formulas and the types
    (dynamic library).
    Then build a prover script and retrieve entailment judgement.
    If results are not conclusive, attempt basic abduction.
    """
    coq_scripts = []
    formulas = get_formulas_from_doc(doc)
    if not formulas:
        return 'unknown', coq_scripts
    dynamic_library_str = get_dynamic_library_from_doc(doc, formulas)

    knowledge_axioms = build_knowledge_axioms(doc.xpath('//ccg'))
    dynamic_library_str += '\n\n' + knowledge_axioms
    premises, conclusion = formulas[:-1], formulas[-1]
    inference_result, coq_script = \
      prove_statements(premises, conclusion, dynamic_library_str)
    coq_scripts.append(coq_script)
    if inference_result:
        inference_result_str = 'yes'
    else:
        negated_conclusion = negate_conclusion(conclusion)
        inference_result, coq_script = \
          prove_statements(premises, negated_conclusion, dynamic_library_str)
        coq_scripts.append(coq_script)
        if inference_result:
            inference_result_str = 'no'
        else:
            inference_result_str = 'unknown'
    return inference_result_str, coq_scripts

# Check whether the string "is defined" appears in the output of coq.
# In that case, we return True. Otherwise, we return False.
def is_theorem_defined(output_lines):
    for output_line in output_lines:
        if len(output_line) > 2 and 'is defined' in (' '.join(output_line[-2:])):
            return True
    return False

def resolve_prefix_to_infix_operations(expr_str, pred = 'R', symbol = '', brackets = ['', '']):
    cat_expr_str = expr_str
    i = 0
    while (pred + '(') in cat_expr_str:
        cat_expr_str = \
          re.sub(pred + r'\(([^' + pred + r']+?),([^' + pred + r']+?)\)',
                 brackets[0] + r'\1' + symbol + r'\2' + brackets[1], cat_expr_str)
        i += 1
        if i > 100:
            logging.warning('There is probably a problem in the resolution of ' \
                    'concatenation expressions in {0}'.format(expr_str))
    return cat_expr_str

def substitute_invalid_chars(script, replacement_filename):
    with codecs.open(replacement_filename, 'r', 'utf-8') as finput:
        repl = dict(line.strip().split() for line in finput)
        for invalid_char, valid_char in repl.items():
            script = script.replace(invalid_char, valid_char)
    return script

_tactics = 'Set Firstorder Depth 1. nltac. Set Firstorder Depth 6. nltac. Qed.'
try:
    with open('tactics_coq.txt') as fin:
        _tactics = fin.read().strip()
except:
    pass

# This function receives two arguments. The first one is a list of the logical
# interpretations of the premises (only one interpretation per premise).
# The second argument is a string with a single interpretation of the conclusion.
def prove_statements(premise_interpretations, conclusion, dynamic_library = ''):
    # Transform these interpretations into coq format:
    #   interpretation1 -> interpretation2 -> ... -> conclusion
    interpretations = premise_interpretations + [conclusion]
    interpretations = [normalize_interpretation(interp) for interp in interpretations]
    coq_formulae = ' -> '.join(interpretations)
    # Input these formulae to coq and retrieve the results.
    input_coq_script = ('echo \"Require Export coqlib.\n'
        '{0}\nTheorem t1: {1}. {2}.\" | coqtop').format(
        dynamic_library, coq_formulae, _tactics)
    # input_coq_script = 'echo \"Require Export coqlib. \n' \
    #   + dynamic_library + '\n' \
    #   + 'Theorem t1: ' + \
    #   coq_formulae + \
    #   '. ' + _tactics + '\" | coqtop'
    # Set Firstorder Depth 1. nltac. nltac_set; nltac_final. Set Firstorder Depth 3. nltac_final. Qed.\" | coqtop'
    input_coq_script = substitute_invalid_chars(input_coq_script, 'replacement.txt')
    # print(input_coq_script)
    process = subprocess.Popen(\
      input_coq_script, \
      shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    output_lines = [str(line).strip().split() for line in process.stdout.readlines()]
    return is_theorem_defined(output_lines), input_coq_script

# Given a string reprsenting the logical interpretation of the conclusion,
# it returns a string with the negated conclusion.
def negate_conclusion(conclusion):
    return '~(' + conclusion + ')'
