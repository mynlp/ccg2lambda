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
import subprocess
from subprocess import check_output

from knowledge import get_lexical_relations
from nltk2coq import normalize_interpretation
from semantic_types import get_dynamic_library_from_doc
from tactics import get_tactics
from theorem import Theorem

def build_knowledge_axioms(doc):
    if not doc:
        return ''
    axioms = get_lexical_relations(doc)
    axioms_str = ""
    for axiom in axioms:
        axioms_str += axiom + '\n'
        axiom_name = axiom.split()[1]
        axioms_str += 'Hint Resolve {0}.\n'.format(axiom_name)
    axioms_str += '\n'
    return axioms_str

# def get_formulas_from_doc(doc):
#     """
#     Returns string representations of logical formulas,
#     as stored in the "sem" attribute of the root node
#     of semantic trees.
#     If a premise has no semantic representation, it is ignored.
#     If there are no semantic representation at all, or the conclusion
#     has no semantic representation, it returns None to signal an error.
#     """
#     formulas = [s.get('sem', None) for s in doc.xpath('./sentences/sentence/semantics/span[1]')]
#     if len(formulas) < 2 or formulas[-1] == None:
#         return None
#     formulas = [f for f in formulas if f is not None]
#     return formulas

def prove_doc(doc, abduction=None):
    """
    Retrieve from trees the logical formulas and the types
    (dynamic library).
    Then build a prover script and retrieve entailment judgement.
    If results are not conclusive, attempt basic abduction.
    """
    theorem = Theorem.from_doc(doc)
    theorem.prove(abduction)
    return theorem

def prove_doc_(doc, abduction=None):
    """
    Retrieve from trees the logical formulas and the types
    (dynamic library).
    Then build a prover script and retrieve entailment judgement.
    If results are not conclusive, attempt basic abduction.
    """
    coq_scripts = []
    failure_logs = []
    formulas = get_formulas_from_doc(doc)
    if not formulas or len(formulas) < 2:
        return 'unknown', coq_scripts, failure_logs
    dynamic_library_str, formulas = get_dynamic_library_from_doc(doc, formulas)

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
    if abduction and inference_result_str == 'unknown':
        inference_result_str, abduction_scripts, failure_logs = \
            abduction.attempt(coq_scripts, doc)
        coq_scripts.extend(abduction_scripts)
    return inference_result_str, coq_scripts, failure_logs

# Check whether the string "is defined" appears in the output of coq.
# In that case, we return True. Otherwise, we return False.
# def is_theorem_defined(output_lines):
#     for output_line in output_lines:
#         if len(output_line) > 2 and 'is defined' in (' '.join(output_line[-2:])):
#             return True
#     return False

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

# def substitute_invalid_chars(script, replacement_filename):
#     with codecs.open(replacement_filename, 'r', 'utf-8') as finput:
#         repl = dict(line.strip().split() for line in finput)
#         for invalid_char, valid_char in repl.items():
#             script = script.replace(invalid_char, valid_char)
#     return script

# This function receives two arguments. The first one is a list of the logical
# interpretations of the premises (only one interpretation per premise).
# The second argument is a string with a single interpretation of the conclusion.
# def prove_statements(premise_interpretations, conclusion, dynamic_library = ''):
#     # Transform these interpretations into coq format:
#     #   interpretation1 -> interpretation2 -> ... -> conclusion
#     interpretations = premise_interpretations + [conclusion]
#     interpretations = [normalize_interpretation(interp) for interp in interpretations]
#     coq_formulae = ' -> '.join(interpretations)
#     # Input these formulae to coq and retrieve the results.
#     tactics = get_tactics()
#     input_coq_script = ('echo \"Require Export coqlib.\n'
#         '{0}\nTheorem t1: {1}. {2}.\" | coqtop').format(
#         dynamic_library, coq_formulae, tactics)
#     input_coq_script = substitute_invalid_chars(input_coq_script, 'replacement.txt')
#     coq_script = "Require Export coqlib.\n{0}\nTheorem t1: {1}. {2}.".format(
#         dynamic_library, coq_formulae, tactics)
#     coq_script = substitute_invalid_chars(coq_script, 'replacement.txt')
# 
#     ps = subprocess.Popen(('echo', coq_script), stdout=subprocess.PIPE)
#     output = subprocess.check_output(
#         ('coqtop',),
#         stdin=ps.stdout,
#         stderr=subprocess.STDOUT,
#         timeout=100)
#     ps.wait()
#     output_lines = [
#         str(line).strip().split() for line in output.decode('utf-8').split('\n')]
#     return is_theorem_defined(output_lines), input_coq_script

# Given a string reprsenting the logical interpretation of the conclusion,
# it returns a string with the negated conclusion.
# def negate_conclusion(conclusion):
#     return - conclusion
