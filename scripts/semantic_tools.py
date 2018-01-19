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

import logging
import re

from knowledge import get_lexical_relations
from semantic_types import get_dynamic_library_from_doc
from theorem import Theorem
from theorem import MasterTheorem
from theorem import get_formulas_from_doc

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

def prove_doc(doc, abduction=None, args=None):
    """
    Retrieve from trees the logical formulas and the types
    (dynamic library).
    Then build a prover script and retrieve entailment judgement.
    If results are not conclusive, attempt basic abduction.
    """
    # TODO: parameterize the switch to choose the type of theorem...
    # .. unless the MasterTheorem mechanism is a complete generalization.
    # theorem = Theorem.from_doc(doc)
    theorem = MasterTheorem.from_doc(doc, args)
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
    # TODO: check this for n-best.
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

