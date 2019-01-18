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
from collections import defaultdict
from copy import deepcopy
import functools
import logging
import re

from nltk import Tree
from nltk.compat import string_types
from nltk.sem.logic import ENTITY_TYPE
from nltk.sem.logic import TRUTH_TYPE
from nltk.sem.logic import EVENT_TYPE
from nltk.sem.logic import ANY_TYPE
from nltk.sem.logic import AbstractVariableExpression
from nltk.sem.logic import ComplexType
from nltk.sem.logic import ConstantExpression
from nltk.sem.logic import NegatedExpression
from nltk.sem.logic import BinaryExpression
from nltk.sem.logic import ApplicationExpression
from nltk.sem.logic import VariableBinderExpression
from nltk.sem.logic import InconsistentTypeHierarchyException
from nltk.sem.logic import Variable
from nltk.sem.logic import typecheck

from knowledge import get_tokens_from_xml_node
from logic_parser import lexpr
from normalization import normalize_token, substitute_invalid_chars
from tree_tools import tree_or_string

COQLIB_PATH='coqlib.v'
def get_reserved_preds_from_coq_static_lib(coq_static_lib_path):
    finput = codecs.open(coq_static_lib_path, 'r', 'utf-8')
    type_definitions = \
        [line.strip() for line in finput if line.startswith('Parameter ')]
    finput.close()
    reserved_predicates = \
        [type_definition.split()[1] for type_definition in type_definitions]
    return reserved_predicates
RESERVED_PREDS=get_reserved_preds_from_coq_static_lib(COQLIB_PATH)

def linearize_type(pred_type):
    linearized_type = []
    if not pred_type.__dict__:
        if str(pred_type) == 'e':
            type_str = 'Entity'
        elif str(pred_type) == 'v':
            type_str = 'Event'
        else:
            type_str = 'Prop'
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
    if expr_type is None:
        return 0
    if 'first' not in expr_type.__dict__ \
       and 'second' not in expr_type.__dict__:
        return 1
    if 'first' in expr_type.__dict__:
        acc_first = type_length(expr_type.first)
    if 'second' in expr_type.__dict__:
        acc_second = type_length(expr_type.second)
    return acc_first + acc_second

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
        except AttributeError as e:
            break
        i += 1
        if i > 100:
            logging.info('There is probably a problem in the typecheck resolution of ' \
                    'expression {0} with signature {1}'.format(str(expr), signature))
            break
    try:
        signature = expr.typecheck(signature)
    except InconsistentTypeHierarchyException as e:
        e_str = str(e)
        variable_name = re.findall(r"'(\S+?)'", e_str)[0]
        signature.pop(variable_name, None)
    except AttributeError as e:
        logging.info('There is probably a problem in the typecheck resolution of ' \
            'expression {0} with signature {1}'.format(str(expr), signature))
    return signature

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

def combine_signatures_safe(signatures):
    """
    Combinator function necessary for .visit method.
    """
    combined_signature = defaultdict(list)
    for signature in signatures:
        for predicate, predtypes_exprs in signature.items():
            for predtype, expr in predtypes_exprs:
                combined_signature[predicate].append((predtype, expr))
    return combined_signature

def convert_to_multitypes(signature, expr):
    multi_signature = defaultdict(list)
    for k, v in signature.items():
        multi_signature[k].append((v, expr))
    return multi_signature

def resolve_types_rec(expr, signature=None):
    """
    Function that is used to traverse the structure of a NLTK formula
    and infer types bottom up, resolving unknowns '?' into 't' (Prop).
    """
    if signature is None:
        signature = defaultdict(list)
    try:
        signature = convert_to_multitypes(expr.typecheck(), expr)
    except InconsistentTypeHierarchyException as e:
        if isinstance(expr, ConstantExpression) or \
           isinstance(expr, AbstractVariableExpression):
            signature = convert_to_multitypes(expr.typecheck(), expr)
        else:
            signature = expr.visit(lambda e: resolve_types_rec(e, signature),
                                   lambda parts: combine_signatures_safe(parts))
    return signature

def make_new_pred_name(pred, pred_type):
    if pred in RESERVED_PREDS:
        return pred
    type_len = type_length(pred_type)
    if type_len > 2:
        pred_name = '{0}_{1}{2}'.format(str(pred), str(pred_type.first), type_len)
    elif type_len == 2:
        pred_name = '{0}_{1}{2}'.format(str(pred), str(pred_type.first), type_len)
    else:
        pred_name = '{0}_{1}{2}'.format(str(pred), str(pred_type), type_len)
    return pred_name

def rename_guided(expr, resolution_guide):
    """
    resolution_guide is a dictionary whose keys are expressions
    and values are tuples (previous_pred, new_pred) that guide
    the renaming.
    """
    replacements = resolution_guide.get(expr, [])
    for prev_pred, new_pred in replacements:
        expr = expr.replace(Variable(prev_pred), lexpr(new_pred))
    return expr

def replace_function_names(expr, resolution_guide, active=None):
    if active is None:
        active = {}
    else:
        active = dict(active)
    if expr in resolution_guide:
        for prev_pred, new_pred in resolution_guide[expr]:
            active[prev_pred] = new_pred
    if isinstance(expr, ConstantExpression) or \
       isinstance(expr, AbstractVariableExpression) or \
       isinstance(expr, Variable):
        return expr
    elif isinstance(expr, NegatedExpression):
        expr.term = replace_function_names(expr.term, resolution_guide, active)
        return expr
    elif isinstance(expr, BinaryExpression):
        child_exprs = [expr.first,  expr.second]
        exprs = [replace_function_names(e, resolution_guide, active) for e in child_exprs]
        expr.first = exprs[0]
        expr.second = exprs[1]
    elif isinstance(expr, ApplicationExpression):
        func, args = expr.uncurry()
        if str(func) in active:
            func = type(func)(Variable(active[str(func)]))
        args_exprs = [replace_function_names(e, resolution_guide, active) for e in args]
        exprs = [func] + args_exprs
        expr = functools.reduce(lambda f, a: ApplicationExpression(f, a), exprs)
    elif isinstance(expr, VariableBinderExpression):
        child_exprs = [expr.variable,  expr.term]
        exprs = [replace_function_names(e, resolution_guide, active) for e in child_exprs]
        expr.variable = exprs[0]
        expr.term = exprs[1]
    else:
        raise NotImplementedError(
            'Expression not recognized: {0}, type: {1}'.format(expr, type(expr)))
    return expr

def combine_signatures_or_rename_preds(exprs, preferred_sigs=None):
    """
    `signatures` is a list of dictionaries. Each dictionary has key-value
      pairs where key is a predicate name, and value is a type object.
    `exprs` are logical formula objects.
    This function return a single signature dictionary with merged signatures.
    If there is a predicate for which there are differing types, then the
    predicate is renamed and each version is associated to a different type
    in the signature dictionary. The target predicate is also renamed in
    the logical expressions.
    """
    if preferred_sigs is None:
        preferred_sigs = [{}] * len(exprs)
    elif isinstance(preferred_sigs, dict):
        preferred_sigs = [preferred_sigs]
    signatures = [resolve_types_rec(expr) for expr in exprs]
    signature = defaultdict(list)
    for s, preferred_sig in zip(signatures, preferred_sigs):
        for pred, type_and_expr_list in s.items():
            pred_types = set([te[0] for te in type_and_expr_list])
            if pred in preferred_sig and len(pred_types.difference(set([preferred_sig[pred]]))) > 0:
                type_and_expr_list = [(preferred_sig[pred], te[1]) for te in type_and_expr_list]
            signature[pred].extend(type_and_expr_list)
    
    resolution_guide = defaultdict(list)
    for pred, sigs_exprs in signature.items():
        if len(sigs_exprs) > 1 and len(set(pred_type for (pred_type, _) in sigs_exprs)) > 1:
            for pred_type, ex in sigs_exprs:
                new_pred_name = make_new_pred_name(pred, pred_type)
                if (pred, new_pred_name) not in resolution_guide[ex]:
                    resolution_guide[ex].append((pred, new_pred_name))

    resolution_guide_local = deepcopy(resolution_guide)
    new_exprs = []
    for expr in exprs:
        if not isinstance(expr, ConstantExpression):
            expr = replace_function_names(expr, resolution_guide_local)
        new_exprs.append(expr)
    signature = type_check_safe(new_exprs)
    signature = combine_signatures(preferred_sigs + [signature])

    signature = remove_reserved_predicates(signature)
    signature = resolve_types_in_signature(signature)
    for expr in exprs:
        signature = remove_colliding_predicates(signature, expr)
    signature = resolve_types_in_signature(signature)
    return signature, new_exprs

def type_check_safe(exprs):
    """
    Returns the signature most specific (longest), ignoring type conflicts.
    """
    signatures = [resolve_types_rec(expr) for expr in exprs]
    combined_signature = {}
    for signature in signatures:
        for predicate, predicate_types_exprs in signature.items():
            types = [te[0] for te in predicate_types_exprs]
            assert len(types) > 0
            types.sort(key=lambda t: type_length(t), reverse=True)
            if predicate not in combined_signature:
                combined_signature[predicate] = types[0]
            else:
                sig_length_previous = type_length(combined_signature[predicate])
                sig_length_new = type_length(types[0])
                if sig_length_new > sig_length_previous:
                    combined_signature[predicate] = types[0]
    return combined_signature

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

def get_dynamic_library_from_doc(doc, semantics_nodes):
    # Each type is of the form "predicate : basic_type -> ... -> basic_type."
    types_sets = []
    for semantics_node in semantics_nodes:
      types = set(semantics_node.xpath('./span/@type'))
      types_sets.append(types)
    types_sets = [[substitute_invalid_chars(t, 'replacement.txt') for t in types] for types in types_sets]
    coq_libs = [['Parameter {0}.'.format(t) for t in types] for types in types_sets]
    nltk_sigs_arbi = [convert_coq_signatures_to_nltk(coq_lib) for coq_lib in coq_libs]
    nltk_sig_arbi = combine_signatures(nltk_sigs_arbi)

    formulas = [sem.xpath('./span[1]/@sem')[0] for sem in semantics_nodes]
    formulas = parse_exprs_if_str(formulas)
    nltk_sig_auto, formulas = combine_signatures_or_rename_preds(formulas, nltk_sigs_arbi)
    # coq_static_lib_path is useful to get reserved predicates.
    # ccg_xml_trees is useful to get full list of tokens
    # for which we need to specify types.
    dynamic_library = merge_dynamic_libraries(
        nltk_sig_arbi,
        nltk_sig_auto,
        doc=doc)
    dynamic_library_str = '\n'.join(sorted(dynamic_library))
    return dynamic_library_str, formulas

def build_library_entry(predicate, pred_type):
    """
    Creates a library entry out of a pair (predicate, pred_type),
    where pred_type is a tree such as <e, t> or <e, <e, t>>, etc.
    It returns a string of the form
    "Parameter pred : Entity -> Prop."
    """
    type_str = str(pred_type).replace(
        '<', '(').replace(
        '>', ')').replace(
        ',', ' -> ').replace(
        't', 'Prop').replace(
        'e', 'Entity').replace(
        'v', 'Event')
    if type_str.endswith(')'):
       type_str = type_str[1:-1]
    library_entry = 'Parameter ' \
                  + predicate \
                  + ' : ' \
                  + type_str \
                  + '.'
    return library_entry

def parse_exprs_if_str(exprs):
    """
    If expressions are strings, convert them into logic formulae.
    """
    exprs_logic = []
    for expr in exprs:
        if isinstance(expr, str):
            exprs_logic.append(lexpr(expr))
        else:
            exprs_logic.append(expr)
    return exprs_logic

def build_dynamic_library(exprs, preferred_signature=None):
    """
    Create a dynamic library with types of objects that appear in coq formulae.
    Optionally, it may receive partially specified signatures for objects
    using the format by NLTK (e.g. {'_john' : e, '_mary' : e, '_love' : <e,<e,t>>}).
    """
    # If expressions are strings, convert them into logic formulae.
    exprs_logic = parse_exprs_if_str(exprs)
    signature, exprs = combine_signatures_or_rename_preds(
        exprs_logic, preferred_signature)
    signature = remove_reserved_predicates(signature)
    return signature, exprs

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
    nltk_type_str = ' '.join(type_sig).rstrip('.').replace(
        '->', ' ').replace(
        'Entity', 'e').replace(
        'Prop', 't').replace(
        'Event', 'v')
    if not nltk_type_str.startswith('(') or not nltk_type_str.endswith('('):
        nltk_type_str = '(' + nltk_type_str + ')'
    # Add pre-terminals (necessary for NLTK, if we convert to CNF).
    nltk_type_str = re.sub(r'([evt])', r'(N \1)', nltk_type_str)
    nltk_type_tree = tree_or_string(nltk_type_str)
    nltk_type_tree.chomsky_normal_form(factor='right')
    nltk_type_str = remove_labels_and_unaries(nltk_type_tree).replace(
        '( ', '(').replace(
        '(', '<').replace(
        ')', '>').replace(
        ' ', ',')
    if len(type_sig) == 1:
        nltk_type_str = nltk_type_str.strip('<>')
    return {surface : read_type(nltk_type_str)}

def remove_labels_and_unaries(tree):
    assert isinstance(tree, Tree)
    leaf_treepos = tree.treepositions(order='leaves')
    for p in tree.treepositions():
        if p not in leaf_treepos and p != ():
            tree[p].set_label('')
            if len(tree[p]) == 1:
                tree[p] = tree[p][0]
    return str(tree)

def read_type(type_string):
    assert isinstance(type_string, string_types)
    type_string = type_string.replace(' ', '') #remove spaces

    if type_string[0] == '<':
        assert type_string[-1] == '>'
        paren_count = 0
        for i,char in enumerate(type_string):
            if char == '<':
                paren_count += 1
            elif char == '>':
                paren_count -= 1
                assert paren_count > 0
            elif char == ',':
                if paren_count == 1:
                    break
        return ComplexType(read_type(type_string[1  :i ]),
                           read_type(type_string[i+1:-1]))
    elif type_string[0] == "%s" % ENTITY_TYPE:
        return ENTITY_TYPE
    elif type_string[0] == "%s" % TRUTH_TYPE:
        return TRUTH_TYPE
    elif type_string[0] == "%s" % EVENT_TYPE:
        return EVENT_TYPE
    elif type_string[0] == "%s" % ANY_TYPE:
        return ANY_TYPE
    else:
        message="Unexpected character: '%s'." % type_string[0]
        raise ValueError(message)

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
    colliding_predicates = set()
    for coq_type in coq_sig:
        nltk_type = convert_coq_to_nltk_type(coq_type)
        for pred, typ in nltk_type.items():
            if pred in nltk_sig:
                colliding_predicates.add(pred)
        nltk_sig.update(nltk_type)
    for pred in colliding_predicates:
        del nltk_sig[pred]
    return nltk_sig

def get_coq_types(xml_node):
    types = xml_node.get('coq_type', None)
    if types is None or types == "":
        return []
    types = types.split(' ||| ')
    return types

def get_predicate_type_from_library(predicate, lib):
    assert isinstance(lib, dict)
    return lib.get(predicate, None)

def merge_dynamic_libraries(sig_arbi, sig_auto, doc):
    # reserved_predicates = get_reserved_preds_from_coq_static_lib(coq_static_lib_path)
    # Get base forms, unless the base form is '*', in which case get surf form.
    base_forms = get_tokens_from_xml_node(doc)
    base_forms = [substitute_invalid_chars(t, 'replacement.txt') for t in base_forms]
    required_predicates = set(normalize_token(t) for t in base_forms)
    sig_merged = sig_auto
    sig_merged.update(sig_arbi) # overwrites automatically inferred types.
    # Remove predicates that are reserved or not required (e.g. variables).
    preds_to_remove = set()
    preds_to_remove.update(RESERVED_PREDS)
    for pred in sig_merged:
        if pred not in required_predicates and not re.match(r'\S+_[a-z][0-9]', pred):
            preds_to_remove.add(pred)
    for pred in preds_to_remove:
        if pred in sig_merged:
            del sig_merged[pred]
    # Convert into coq style library entries.
    dynamic_library = []
    for predicate, pred_type in sig_merged.items():
        library_entry = build_library_entry(predicate, pred_type)
        dynamic_library.append(library_entry)
    result_lib = list(set(dynamic_library))
    return result_lib

