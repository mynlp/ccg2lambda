#!/usr/bin/python
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

import codecs
from collections import OrderedDict
import subprocess

from coq_analyzer import analyze_coq_output
from nltk2coq import normalize_interpretation
from semantic_types import get_dynamic_library_from_doc
from tactics import get_tactics

class Theorem(object):
    """
    Manage a theorem and its variations.
    """

    def __init__(self, premises, conclusion, axioms=None, is_negated=False):
        self.premises = premises
        self.conclusion = conclusion
        self.axioms = set() if axioms is None else axioms
        self.dynamic_library_str = None
        self.inference_result = None
        self.coq_script = None
        self.is_negated = is_negated
        self.variations = []
        self.doc = None
        self.failure_log = None

    def __repr__(self):
        return self.coq_script

    def __hash__(self):
        return hash(self.coq_script)

    def __eq__(self, other):
        return isinstance(other, Theorem) and self.coq_script == other.coq_script

    @staticmethod
    def from_doc(doc):
        """
        Build a theorem from an XML document produced by semparse.py script.
        """
        formulas = get_formulas_from_doc(doc)
        if not formulas or len(formulas) < 2:
            return Theorem([], '', set())
        dynamic_library_str, formulas = get_dynamic_library_from_doc(doc, formulas)
        premises, conclusion = formulas[:-1], formulas[-1]
        theorem = Theorem(premises, conclusion, set())
        theorem.dynamic_library_str = dynamic_library_str
        theorem.doc = doc
        return theorem

    def copy(self, new_premises=None, new_conclusion=None, new_axioms=None, is_negated=None):
        if new_premises is None:
            new_premises = self.premises
        if new_conclusion is None:
            new_conclusion = self.conclusion
        if new_axioms is None:
            new_axioms = self.axioms
        if is_negated is None:
            is_negated = self.is_negated
        theorem = Theorem(
            new_premises, new_conclusion, new_axioms, is_negated=is_negated)
        theorem.dynamic_library_str = self.dynamic_library_str
        theorem.is_negated = is_negated
        theorem.doc = self.doc
        self.variations.append(theorem)
        return theorem

    def negate(self):
        negated_conclusion = negate_conclusion(self.conclusion)
        theorem = self.copy(
            new_conclusion=negated_conclusion,
            is_negated=not self.is_negated)
        return theorem

    @property
    def result(self):
        for theorem in self.variations:
            if theorem.result_simple != 'unknown':
                return theorem.result_simple
        return 'unknown'

    @property
    def result_simple(self):
        if self.inference_result is True and self.is_negated is False:
            return 'yes'
        elif self.inference_result is True and self.is_negated is True:
            return 'no'
        else:
            return 'unknown'

    def prove_debug(self, axioms=None):
        failure_log = OrderedDict()
        coq_script = make_coq_script(
            self.premises,
            self.conclusion,
            self.dynamic_library_str,
            axioms=axioms)
        current_tactics = get_tactics()
        debug_tactics = 'repeat nltac_base. try substitution. Qed'
        coq_script = coq_script.replace(current_tactics, debug_tactics)
        output_lines = run_coq_script(coq_script)

        if is_theorem_defined(output_lines):
            if axioms == self.axioms:
                self.inference_result = True
                self.coq_script = coq_script
                self.failure_log = failure_log
            return True, failure_log

        failure_log = analyze_coq_output(output_lines)
        return False, failure_log

    def prove_simple(self):
        self.coq_script = make_coq_script(
            self.premises,
            self.conclusion,
            self.dynamic_library_str,
            self.axioms)
        self.inference_result = prove_script(self.coq_script)
        # self.inference_result, self.coq_script = prove_statements(
        #     self.premises, self.conclusion, self.dynamic_library_str)
        return

    def prove(self, abduction=None):
        self.prove_simple()
        self.variations.append(self)
        if self.inference_result is False:
            neg_theorem = self.negate()
            neg_theorem.prove_simple()
        # from pudb import set_trace; set_trace()
        if abduction and self.result == 'unknown' and self.doc is not None:
            abduction.attempt(self)
        return

    def reverse(self):
        if len(self.premises) != 1:
            return None
        return self.copy([self.conclusion], self.premises[0])

def get_formulas_from_doc(doc):
    """
    Returns string representations of logical formulas,
    as stored in the "sem" attribute of the root node
    of semantic trees.
    If a premise has no semantic representation, it is ignored.
    If there are no semantic representation at all, or the conclusion
    has no semantic representation, it returns None to signal an error.
    """
    formulas = [s.get('sem', None) for s in doc.xpath('./sentences/sentence/semantics/span[1]')]
    if len(formulas) < 2 or formulas[-1] == None:
        return None
    formulas = [f for f in formulas if f is not None]
    return formulas

def make_coq_script(premise_interpretations, conclusion, dynamic_library = '', axioms=None):
    # Transform these interpretations into coq format:
    #   interpretation1 -> interpretation2 -> ... -> conclusion
    interpretations = premise_interpretations + [conclusion]
    interpretations = [normalize_interpretation(interp) for interp in interpretations]
    coq_formulae = ' -> '.join(interpretations)
    # Input these formulae to coq and retrieve the results.
    tactics = get_tactics()
    coq_script = "Require Export coqlib.\n{0}\nTheorem t1: {1}. {2}.".format(
        dynamic_library, coq_formulae, tactics)
    if axioms is not None:
        coq_script = insert_axioms_in_coq_script(axioms, coq_script)
    coq_script = substitute_invalid_chars(coq_script, 'replacement.txt')
    return coq_script

def prove_script(coq_script):
    output_lines = run_coq_script(coq_script)
    return is_theorem_defined(output_lines)

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
# 
#     output_lines = run_coq_script(coq_script)
#     return is_theorem_defined(output_lines), input_coq_script

def run_coq_script(coq_script, timeout=100):
    """
    Receives coq script of the form:
      Require Export coqlib.
      Parameter ...
      Parameter ...
      Theorem t1 ... <tactics>. Qed.
    Returns the output lines.
    """
    coq_script = substitute_invalid_chars(coq_script, 'replacement.txt')
    ps = subprocess.Popen(('echo', coq_script), stdout=subprocess.PIPE)
    output = subprocess.check_output(
        ('coqtop',),
        stdin=ps.stdout,
        stderr=subprocess.STDOUT,
        timeout=timeout)
    ps.wait()
    output_lines = [
        str(line).strip() for line in output.decode('utf-8').split('\n')]
    return output_lines

def substitute_invalid_chars(script, replacement_filename):
    with codecs.open(replacement_filename, 'r', 'utf-8') as finput:
        repl = dict(line.strip().split() for line in finput)
        for invalid_char, valid_char in repl.items():
            script = script.replace(invalid_char, valid_char)
    return script

# Given a string reprsenting the logical interpretation of the conclusion,
# it returns a string with the negated conclusion.
def negate_conclusion(conclusion):
    return - conclusion

# Check whether the string "is defined" appears in the output of coq.
# In that case, we return True. Otherwise, we return False.
def is_theorem_defined(output_lines):
    for output_line in output_lines:
        if len(output_line) > 2 and 'is defined' in output_line:
            return True
    return False

def is_theorem_error(output_lines):
    """
    Errors in the construction of a theorem (type mismatches in axioms, etc.)
    are signaled using the symbols ^^^^ indicating where the error is.
    We simply search for that string.
    """
    return any('^^^^' in ol for ol in output_lines)

def get_theorem_line(coq_script_lines):
    for i, line in enumerate(coq_script_lines):
        if line.startswith('Theorem '):
            return i
    assert False, 'There was no theorem defined in the coq script: {0}'\
        .format('\n'.join(coq_script_lines))

def insert_axioms_in_coq_script(axioms, coq_script):
    coq_script_lines = coq_script.split('\n')
    theorem_line = get_theorem_line(coq_script_lines)
    for axiom in axioms:
        axiom_name = axiom.split()[1]
        coq_script_lines.insert(
            theorem_line, 'Hint Resolve {0}.'.format(axiom_name))
        coq_script_lines.insert(theorem_line, axiom)
    new_coq_script = '\n'.join(coq_script_lines)
    return new_coq_script

