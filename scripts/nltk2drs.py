# -*- coding: utf-8 -*-

import nltk
from nltk.sem.drt import *

from logic_parser import lexpr
from nltk2normal import *

dp = nltk.sem.DrtExpression.fromstring

def convert_to_drs(expression):
    expression = rename_variable(expression)
    expression = remove_true(expression)
    drs_expr = convert_drs(DRS([],[]), expression)
    return drs_expr

def convert_drs(contextdrs, expression):
    if isinstance(expression, ApplicationExpression):
        drs_expr = convert_drs_application(contextdrs, expression)
    elif isinstance(expression, EqualityExpression):
        drs_expr = convert_drs_equality(contextdrs, expression)
    elif isinstance(expression, AndExpression):
        drs_expr = convert_drs_and(contextdrs, expression)
    elif isinstance(expression, OrExpression):
        drs_expr = convert_drs_or(contextdrs, expression)
    elif isinstance(expression, ImpExpression):
        drs_expr = convert_drs_imp(contextdrs, expression)
    elif isinstance(expression, NegatedExpression):
        drs_expr = convert_drs_not(contextdrs, expression)
    elif isinstance(expression, ExistsExpression):
        drs_expr = convert_drs_exists(contextdrs, expression)
    elif isinstance(expression, AllExpression):
        drs_expr = convert_drs_all(contextdrs, expression)
    elif isinstance(expression, LambdaExpression):
        drs_expr = convert_drs_lambda(contextdrs, expression)
    elif isinstance(expression, AbstractVariableExpression):
        variable_str = str(expression.variable).lower()
        if variable_str[0] == '_':
            variable = Variable(variable_str[1:])
        else:
            variable = Variable(variable_str)
        drs_expr = DrtAbstractVariableExpression(variable)
    # elif isinstance(expression, IndividualVariableExpression):
    #     drs_expr = DrtIndividualVariableExpression(expression.variable)
    # elif isinstance(expression, EventVariableExpression):
    #     drs_expr = DrtEventVariableExpression(expression.variable)
    # elif isinstance(expression, FunctionVariableExpression):
    #     drs_expr = DrtFunctionVariableExpression(expression.variable)
    # elif isinstance(expression, ConstantExpression):
    #     drs_expr = DrtConstantExpression(expression.variable)
    else:
        drs_expr = expression
    return drs_expr

functional_terms = ['Subj', 'Obj', 'Nom', 'Acc', 'Dat', 'subj', 'obj', 'nom', 'acc', 'dat', 'this', 'that']
fterms = [ConstantExpression(Variable(expr)) for expr in functional_terms]

def convert_drs_application(contextdrs, expression):
    universe = contextdrs.refs
    conditions = contextdrs.conds
    function, args = expression.uncurry()
    function = convert_drs(DRS([],[]), function)
    # functional terms do not form DRSs
    if function in fterms:
        argument = convert_drs(DRS([],[]), expression.argument)
        drs_expr = DrtApplicationExpression(function, argument)
    elif isinstance(function, DrtLambdaExpression):
        expr = function
        for arg in args:
            argument = convert_drs(DRS([],[]), arg)
            expr = DrtApplicationExpression(expr, argument)
        drs_expr = expr
    else:
        expr = DrtConstantExpression(function.variable)
        for arg in args:
            argument = convert_drs(DRS([],[]), arg)
            expr = DrtApplicationExpression(expr, argument)
        conditions.append(expr)
        drs_expr = DRS(universe, conditions)
    return drs_expr

def convert_drs_equality(contextdrs, expression):
    universe = contextdrs.refs
    conditions = contextdrs.conds
    first = convert_drs(DRS([],[]), expression.first)
    second = convert_drs(DRS([],[]), expression.second)
    expr = DrtEqualityExpression(first, second)
    conditions.append(expr)
    drs_expr = DRS(universe, conditions)
    return drs_expr

def convert_drs_and(contextdrs, expression):
    first = convert_drs(contextdrs, expression.first)
    drs_expr = convert_drs(first, expression.second)
    return drs_expr

def convert_drs_or(contextdrs, expression):
    universe = contextdrs.refs
    conditions = contextdrs.conds
    first = convert_drs(DRS([],[]), expression.first)
    second = convert_drs(DRS([],[]), expression.second)
    expr = DrtOrExpression(first, second)
    conditions.append(expr)
    drs_expr = DRS(universe, conditions)
    return drs_expr

def convert_drs_imp(contextdrs, expression):
    universe = contextdrs.refs
    conditions = contextdrs.conds
    first = convert_drs(DRS([],[]), expression.first)
    second = convert_drs(DRS([],[]), expression.second)
    expr = DRS(first.refs, first.conds, second)
    conditions.append(expr)
    drs_expr = DRS(universe, conditions)
    return drs_expr

def convert_drs_not(contextdrs, expression):
    universe = contextdrs.refs
    conditions = contextdrs.conds
    term = convert_drs(DRS([],[]), expression.term)
    expr = DrtNegatedExpression(term)
    conditions.append(expr)
    drs_expr = DRS(universe, conditions)
    return drs_expr

def convert_drs_exists(contextdrs, expression):
    universe = contextdrs.refs
    conditions = contextdrs.conds
    variable = expression.variable
    universe.append(variable)
    contextdrs = DRS(universe, conditions)
    drs_expr = convert_drs(contextdrs, expression.term)
    return drs_expr

def convert_drs_all(contextdrs, expression):
    universe = contextdrs.refs
    conditions = contextdrs.conds
    variable = expression.variable
    body = expression.term
    if isinstance(body, ImpExpression):
        antecedent = body.first
        consequent = body.second
        context = DRS([variable],[])
        antecedent_drs = convert_drs(context, antecedent)
        consequent_drs = convert_drs(DRS([],[]), consequent)
        expr = DRS(antecedent_drs.refs, antecedent_drs.conds, consequent_drs)
        conditions.append(expr)
        drs_expr = DRS(universe,conditions)
    else:
        consequent_drs = convert_drs(DRS([],[]), body)
        expr = DRS([variable], [], consequent_drs)
        conditions.append(expr)
        drs_expr = DRS(universe, conditions)
    return drs_expr

def convert_drs_lambda(contextdrs, expression):
    variable = expression.variable
    term = expression.term
    term = convert_drs(DRS([],[]), term)
    drs_expr = DrtLambdaExpression(variable, term)
    return drs_expr
