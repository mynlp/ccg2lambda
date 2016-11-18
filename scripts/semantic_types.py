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

from knowledge import get_lexical_relations, get_tokens_from_xml_node
from logic_parser import lexpr
from nltk2coq import normalize_interpretation
from normalization import normalize_token

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

def get_dynamic_library_from_doc(doc, formulas):
    # Each type is of the form "predicate : basic_type -> ... -> basic_type."
    types = set(doc.xpath('//semantics//@type'))
    coq_lib = ['Parameter {0}.'.format(t) for t in types]
    nltk_sig = convert_coq_signatures_to_nltk(coq_lib)
    coq_lib_augmented = build_dynamic_library(formulas, nltk_sig)
    # coq_static_lib_path is useful to get reserved predicates.
    # ccg_xml_trees is useful to get full list of tokens
    # for which we need to specify types.
    dynamic_library = merge_dynamic_libraries(
        coq_lib=coq_lib,
        nltk_lib=coq_lib_augmented,
        coq_static_lib_path='coqlib.v', 
        doc=doc)
    dynamic_library_str = '\n'.join(dynamic_library)
    return dynamic_library_str

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
    assert parameter == 'Parameter' and colon == ':'
    # This list contains something like ['Entity', '->', 'Prop', '->', 'Prop'...]
    type_sig = coq_type_list[3:]
    type_ids = []
    for i, type_item in enumerate(type_sig):
        assert (i % 2 == 1) == (type_item == '->')
        if type_item.startswith('Entity'):
            type_ids.append('e')
        elif type_item.startswith('Prop'):
            type_ids.append('t')
        elif type_item.startswith('Event'):
            type_ids.append('e')
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

def get_coq_types(xml_node):
    types = xml_node.get('coq_type', None)
    if types is None or types == "":
        return []
    types = types.split(' ||| ')
    return types

def build_arbitrary_dynamic_library(ccg_trees):
    """
    Given a list of CCG trees whose root nodes are annotated with an
    attribute 'coq_type', it produces a list of entries for the dynamic
    library that is piped to coq. The output is something like:
    ["Parameter dog : Entity.", "Parameter walk : Entity -> Prop.", ...]
    """
    dynamic_library = []
    for ccg_tree in ccg_trees:
        coq_types = get_coq_types(ccg_tree)
        dynamic_library.extend(coq_types)
    dynamic_library = sorted(list(set(dynamic_library)))
    return dynamic_library

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

def merge_dynamic_libraries(coq_lib, nltk_lib, coq_static_lib_path, doc):
    reserved_predicates = get_reserved_preds_from_coq_static_lib(coq_static_lib_path)
    # Get base forms, unless the base form is '*', in which case get surf form.
    base_forms = get_tokens_from_xml_node(doc)
    required_predicates = set(normalize_token(t) for t in base_forms)
    # required_predicates = set(normalize_token(t) for t in doc.xpath('//token/@base'))
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
