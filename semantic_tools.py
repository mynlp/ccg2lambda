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

from nltk2coq import normalize_interpretation
from nltk.sem.logic import (typecheck, read_type, ConstantExpression,
  AbstractVariableExpression, InconsistentTypeHierarchyException, LogicParser)
from knowledge import get_lexical_relations, get_tokens_from_ccg_tree
from semantic_rule import lexpr

def get_tree_or_string(tree_str):
    return Tree.fromstring(tree_str) if tree_str.startswith('(') else tree_str

def linearize_type(pred_type):
    linearized_type = []
    if not pred_type.__dict__:
        type_str = 'Entity' if str(pred_type) == 'e' else 'Prop'
        linearized_type = [type_str]
    else:
        linearized_type.extend(linearize_type(pred_type.first))
        linearized_type.extend(linearize_type(pred_type.second))
    return linearized_type

def type_length(expr_type):
    """
    Counts the number of parameters of a predicate. E.g.
    type_length(e) = 1
    type_length(<e, t>) = 2
    type_length(<e, <e,t>>) = 3
    """
    acc_first, acc_second = 0, 0
    if 'first' not in expr_type.__dict__ \
       and 'second' not in expr_type.__dict__:
        return 1
    if 'first' in expr_type.__dict__:
        acc_first = type_length(expr_type.first)
    if 'second' in expr_type.__dict__:
        acc_second = type_length(expr_type.second)
    return acc_first + acc_second

def combine_signatures(signatures):
    """
    Combinator function necessary for .visit method.
    If one predicate is resolved as different types, only the shortest
    (less complex) type is finally assigned.
    """
    combined_signature = {}
    for signature in signatures:
        for predicate, predicate_sig in signature.items():
            if predicate not in combined_signature:
                combined_signature[predicate] = predicate_sig
            else:
                sig_length_previous = type_length(combined_signature[predicate])
                sig_length_new = type_length(predicate_sig)
                if sig_length_new > sig_length_previous:
                    combined_signature[predicate] = predicate_sig
    return combined_signature

def resolve_types_in_signature(signature):
    signature = {k : v for k, v in signature.items() if v is not None}
    for predicate, pred_type in signature.items():
        pred_type_str = str(pred_type)
        pred_type_str_resolved = re.sub(r'\?', r't', pred_type_str)
        signature[predicate] = read_type(pred_type_str_resolved)
    return signature

def remove_colliding_predicates(signature, expr):
    resolution_success = False
    i = 0
    while (not resolution_success):
        try:
            expr.typecheck(signature)
            resolution_success = True
        except InconsistentTypeHierarchyException as e:
            e_str = str(e)
            # The exception message is of the form:
            # The variable ''s' was found in ... (referring to variable 's).
            variable_name = re.findall(r"'(\S+?)'", e_str)[0]
            signature.pop(variable_name, None)
            if variable_name == 'TrueP':
                break
        i += 1
        if i > 100:
            logging.warning('There is probably a problem in the typecheck resolution of ' \
                    'expression {0} with signature {1}'.format(str(expr), signature))
            break
    try:
        signature = expr.typecheck(signature)
    except InconsistentTypeHierarchyException as e:
        e_str = str(e)
        variable_name = re.findall(r"'(\S+?)'", e_str)[0]
        signature.pop(variable_name, None)
    return signature

def resolve_types(expr, signature = {}):
    """
    Function that is used to traverse the structure of a NLTK formula
    and infer types bottom up, resolving unknowns '?' into 't' (Prop).
    """
    if isinstance(expr, ConstantExpression) or \
       isinstance(expr, AbstractVariableExpression):
        return expr.typecheck()
    signature = expr.visit(lambda e: resolve_types(e, signature),
                           lambda parts: combine_signatures(parts))
    signature = remove_reserved_predicates(signature)
    signature = remove_colliding_predicates(signature, expr)
    signature = remove_reserved_predicates(signature)
    signature = resolve_types_in_signature(signature)
    return signature

def remove_reserved_predicates(signature):
    """
    Some predicates are already defined in coq, and they are not necessary
    to handle here. Moreover, predicates like AND or OR would be difficult
    to handle in this context, because they may have different types in the
    same formuli.
    """
    reserved_predicates = ['AND', 'OR', 'TrueP']
    for reserved_predicate in reserved_predicates:
        if reserved_predicate in signature:
            del signature[reserved_predicate]
    return signature

def build_library_entry(predicate, pred_type):
    """
    Creates a library entry out of a pair (predicate, pred_type),
    where pred_type is a tree such as <e, t> or <e, <e, t>>, etc.
    It returns a string of the form
    "Parameter pred : Entity -> Prop."
    """
    linearized_type = linearize_type(pred_type)
    library_entry = 'Parameter ' \
                  + predicate \
                  + ' : ' \
                  + ' -> '.join(linearized_type) \
                  + '.'
    return library_entry

def build_dynamic_library(exprs, coq_types = {}):
    """
    Create a dynamic library with types of objects that appear in coq formulae.
    Optionally, it may receive partially specified signatures for objects
    using the format by NLTK (e.g. {'_john' : e, '_mary' : e, '_love' : <e,<e,t>>}).
    """
    # If expressions are strings, convert them into logic formulae.
    exprs_logic = []
    for expr in exprs:
        if isinstance(expr, str):
            exprs_logic.append(lexpr(expr))
        else:
            exprs_logic.append(expr)
    signatures = [resolve_types(e) for e in exprs_logic]
    signature = combine_signatures(signatures)
    signature = remove_reserved_predicates(signature)
    dynamic_library = []
    for predicate, pred_type in signature.items():
        library_entry = build_library_entry(predicate, pred_type)
        dynamic_library.append(library_entry)
    return list(set(dynamic_library))

def convert_coq_to_nltk_type(coq_type):
    """
    Given a coq_type specification such as:
      Parameter _love : Entity -> Entity -> Prop.
    return the equivalent NLTK type specification:
      {'_love' : read_type('<e, <e, t>>')}
    """
    assert isinstance(coq_type, str)
    coq_type_list = coq_type.split()
    assert len(coq_type_list) >= 4, 'Wrong coq_type format: %s' % coq_type
    parameter, surface, colon = coq_type_list[:3]
    assert parameter == 'Parameter'
    assert colon == ':'
    # This list contains something like ['Entity', '->', 'Prop', '->', 'Prop'...]
    type_sig = coq_type_list[3:]
    type_ids = []
    for i, type_item in enumerate(type_sig):
        assert (i % 2 == 1) == (type_item == '->')
        if type_item.startswith('Entity'):
            type_ids.append('e')
        elif type_item.startswith('Prop'):
            type_ids.append('t')
        elif type_item != '->':
            raise(ValueError('Invalid type name: %s in %s' % (type_item, coq_type)))
    assert len(type_ids) > 0
    if len(type_ids) == 1:
        nltk_type_str = type_ids[0]
    else:
        # Create a string like "<e, <t, t>>"
        nltk_type_str = '<' + ', <'.join(type_ids[:-1]) \
                      + ', ' + type_ids[-1] + '>' * len(type_ids)
    return {surface : read_type(nltk_type_str)}

def convert_coq_signatures_to_nltk(coq_sig):
    """
    Given a coq_library of type specifications such as:
      Parameter _love : Entity -> Entity -> Prop.
      Parameter _john : Entity.
      Parameter _mary : Entity.
    return the equivalent NLTK type specification:
      {'_love' : read_type('<e, <e, t>>'),
       '_john' : read_type('e'),
       '_mary' : read_type('e')}
    """
    assert isinstance(coq_sig, list)
    nltk_sig = {}
    nltk_types = []
    for coq_type in coq_sig:
        nltk_type = convert_coq_to_nltk_type(coq_type)
        nltk_sig.update(nltk_type)
    return nltk_sig

def build_arbitrary_dynamic_library(ccg_trees):
    """
    Given a list of CCG trees whose root nodes are annotated with an
    attribute 'coq_type', it produces a list of entries for the dynamic
    library that is piped to coq. The output is something like:
    ["Parameter dog : Entity.", "Parameter walk : animal -> location.", ...]
    """
    dynamic_library = []
    for ccg_tree in ccg_trees:
        coq_types = simplejson.loads(ccg_tree.attrib.get('coq_type', "[]"))
        dynamic_library.extend(coq_types)
    dynamic_library = sorted(list(set(dynamic_library)))
    return dynamic_library

def build_knowledge_axioms(ccg_trees):
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

def get_reserved_preds_from_coq_static_lib(coq_static_lib_path):
    finput = codecs.open(coq_static_lib_path, 'r', 'utf-8')
    type_definitions = \
      [line.strip() for line in finput if line.startswith('Parameter ')]
    finput.close()
    reserved_predicates = \
      [type_definition.split()[1] for type_definition in type_definitions]
    return reserved_predicates

def get_predicate_type_from_library(predicate, lib):
    assert isinstance(lib, dict)
    return lib.get(predicate, None)

def merge_dynamic_libraries(coq_lib, nltk_lib, coq_static_lib_path, ccg_xml_trees):
    reserved_predicates = get_reserved_preds_from_coq_static_lib(coq_static_lib_path)
    required_predicates = []
    for ccg_xml_tree in ccg_xml_trees:
        tokens_node = ccg_xml_tree.find('.//tokens')
        tokens = [token.get('base') for token in tokens_node]
        required_predicates.extend(tokens)
    required_predicates = list(set(required_predicates))
    # Library entries are of the form:
    # Parameter _predicate : Type1 -> Type2 ...
    # We index library entries by the predicate they define.
    coq_lib_index = {coq_lib_entry.split()[1] : coq_lib_entry \
                       for coq_lib_entry in coq_lib}
    nltk_lib_index = {nltk_lib_entry.split()[1] : nltk_lib_entry \
                        for nltk_lib_entry in nltk_lib}
    result_lib = []
    for predicate in required_predicates:
        if predicate in reserved_predicates:
            continue
        coq_predicate_type = get_predicate_type_from_library(predicate, coq_lib_index)
        nltk_predicate_type = get_predicate_type_from_library(predicate, nltk_lib_index)
        if coq_predicate_type is not None:
            result_lib.append(coq_predicate_type)
        elif nltk_predicate_type is not None:
            result_lib.append(nltk_predicate_type)
    result_lib = list(set(result_lib))
    return result_lib

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

def get_sentences(line):
    sentences = [s.strip() for s in line.split(';')]
    (final_premise, conclusion) = [s.strip() for s in sentences[-1].split('=>')]
    sentences[-1] = final_premise
    sentences.append(conclusion)
    return sentences

# Check whether this line of prolog output contains a formula.
# We know whether it contains a formula or not because the first
# token of the line is a digit.
def is_prolog_result(line):
    if len(line) == 0:
        return False
    return len(set(string.digits).intersection(line[0])) > 0

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
    input_coq_script = 'echo \"Require Export coqlib. \n' \
      + dynamic_library + '\n' \
      + 'Theorem t1: ' + \
      coq_formulae + \
      '. nltac. Qed.\" | coqtop'
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
