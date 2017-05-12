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

from nltk.sem.logic import *

from logic_parser import lexpr

def normalize_interpretation(expression):
    norm_interp_str = coq_string_expr(expression)
    return norm_interp_str

def coq_string_expr(expression):
    if isinstance(expression, str):
        expression = lexpr(expression)
    expr_coq_str = ''
    if isinstance(expression, ApplicationExpression):
        expr_coq_str = coq_string_application_expr(expression)
    elif isinstance(expression, AbstractVariableExpression):
        expr_coq_str = coq_string_abstract_variable_expr(expression)
    elif isinstance(expression, LambdaExpression):
        expr_coq_str = coq_string_lambda_expr(expression)
    elif isinstance(expression, QuantifiedExpression):
        expr_coq_str = coq_string_quantified_expr(expression)
    elif isinstance(expression, AndExpression):
        expr_coq_str = coq_string_and_expr(expression)
    elif isinstance(expression, OrExpression):
        expr_coq_str = coq_string_or_expr(expression)
    elif isinstance(expression, NegatedExpression):
        expr_coq_str = coq_string_not_expr(expression)
    elif isinstance(expression, BinaryExpression):
        expr_coq_str = coq_string_binary_expr(expression)
    elif isinstance(expression, Variable):
        expr_coq_str = '%s' % expression
    else:
        expr_coq_str = str(expression)
    return expr_coq_str

coqstr = coq_string_expr

def coq_string_application_expr(expression):
    # uncurry the arguments and find the base function
    if expression.is_atom():
        function, args = expression.uncurry()
        arg_str = ' '.join("%s" % coqstr(arg) for arg in args)
    else:
        #Leave arguments curried
        function = expression.function
        arg_str = "%s" % coqstr(expression.argument)

    function_str = "%s" % coqstr(function)
    parenthesize_function = False
    if isinstance(function, LambdaExpression):
        if isinstance(function.term, ApplicationExpression):
            if not isinstance(function.term.function,
                              AbstractVariableExpression):
                parenthesize_function = True
        elif not isinstance(function.term, BooleanExpression):
            parenthesize_function = True
    elif isinstance(function, ApplicationExpression):
        parenthesize_function = True

    if parenthesize_function:
        function_str = Tokens.OPEN + function_str + Tokens.CLOSE

    return Tokens.OPEN + function_str + ' ' + arg_str + Tokens.CLOSE

reserved_predicates = \
  {'AND' : 'and', 'OR' : 'or', 'neg' : 'not', 'EMPTY' : '', 'TrueP' : 'True'}
def coq_string_abstract_variable_expr(expression):
    expr_str = str(expression.variable)
    if expr_str in reserved_predicates:
        expr_str = reserved_predicates[expr_str]
    if not isinstance(expression, FunctionVariableExpression):
        if expr_str == '':
            expr_str = "%s" % expr_str
        else:
            expr_str = "%s" % expr_str
    else:
        expr_str = "%s" % expr_str
    return expr_str

def coq_string_lambda_expr(expression):
    variables = [expression.variable]
    term = expression.term
    while term.__class__ == expression.__class__:
        variables.append(term.variable)
        term = term.term
    return Tokens.OPEN + 'fun ' + ' '.join("%s" % coqstr(v) for v in variables) + \
           ' => ' + "%s" % coqstr(term) + Tokens.CLOSE

nltk2coq_quantifier = {'exists' : 'exists',
                       'exist' : 'exists',
                       'all' : 'forall',
                       'forall' : 'forall'}
def coq_string_quantified_expr(expression):
    variables = [expression.variable]
    term = expression.term
    while term.__class__ == expression.__class__:
        variables.append(term.variable)
        term = term.term
    nltk_quantifier = expression.getQuantifier()
    # Rename quantifiers, according to coq notation. Such renaming dictionary
    # is defined above as "nltk2coq_quantifier". If a rename convention is not
    # available, use the same as in NLTK.
    if nltk_quantifier in nltk2coq_quantifier:
        coq_quantifier = nltk2coq_quantifier[expression.getQuantifier()]
    else:
        coq_quantifier = nltk_quantifier
    return Tokens.OPEN + coq_quantifier + ' ' \
           + ' '.join("%s" % coqstr(v) for v in variables) + \
           ', ' + "%s" % coqstr(term) + Tokens.CLOSE

def coq_string_and_expr(expression):
    first = coqstr(expression.first)
    second = coqstr(expression.second)
    return Tokens.OPEN + 'and ' + first + ' ' + second + Tokens.CLOSE

def coq_string_or_expr(expression):
    first = coqstr(expression.first)
    second = coqstr(expression.second)
    return Tokens.OPEN + 'or ' + first + ' ' + second + Tokens.CLOSE

def coq_string_not_expr(expression):
    term_str = coqstr(expression.term)
    return Tokens.OPEN + 'not ' + term_str + Tokens.CLOSE

def coq_string_binary_expr(expression):
    first = coqstr(expression.first)
    second = coqstr(expression.second)
    return Tokens.OPEN + first + ' ' + expression.getOp() \
            + ' ' + second + Tokens.CLOSE
