# -*- coding: utf-8 -*-

from nltk.sem.logic import *
from logic_parser import lexpr
from nltk2normal import rename_variable, remove_true

def convert_to_tptp_proof(formulas):
    if len(formulas) == 1:
        conjecture = formulas[0]
        tptp_script = ['fof(h,conjecture,{0}).'.format(conjecture)]
    else:
        premises, conjecture = formulas[:-1], formulas[-1]
        tptp_script = []
        num = 1
        for formula in premises:
            formula = convert_to_tptp(formula)
            tptp_script.append('fof(t{0},axiom,{1}).'.format(num,formula))
            num += 1
        conjecture = convert_to_tptp(conjecture)
        tptp_script.append('fof(h,conjecture,{0}).'.format(conjecture))
    return tptp_script        

def convert_to_tptp(expression):
    expression = rename_variable(expression)
    expression = remove_true(expression)
    tptp_str = convert_tptp(expression)
    return tptp_str

def convert_tptp(expression):
    if isinstance(expression, ApplicationExpression):
        tptp_str = convert_tptp_application(expression)
    elif isinstance(expression, EqualityExpression):
        tptp_str = convert_tptp_equality(expression)
    elif isinstance(expression, AndExpression):
        tptp_str = convert_tptp_and(expression)
    elif isinstance(expression, OrExpression):
        tptp_str = convert_tptp_or(expression)
    elif isinstance(expression, ImpExpression):
        tptp_str = convert_tptp_imp(expression)
    elif isinstance(expression, IffExpression):
        tptp_str = convert_tptp_iff(expression)
    elif isinstance(expression, NegatedExpression):
        tptp_str = convert_tptp_not(expression)
    elif isinstance(expression, ExistsExpression):
        tptp_str = convert_tptp_exists(expression)
    elif isinstance(expression, AllExpression):
        tptp_str = convert_tptp_all(expression)
    elif isinstance(expression, LambdaExpression):
        tptp_str = convert_tptp_lambda(expression)
    elif isinstance(expression, IndividualVariableExpression):
        tptp_str = str(expression.variable).upper()
    elif isinstance(expression, EventVariableExpression):
        tptp_str = str(expression.variable).upper()
    elif isinstance(expression, FunctionVariableExpression):
        tptp_str = str(expression.variable).upper()
    elif isinstance(expression, ConstantExpression):
        tptp_str = str(expression.variable).lower()
        if tptp_str[0] == '_':
            tptp_str = tptp_str[1:]
    else:
        tptp_str = str(expression)
    return tptp_str

def convert_tptp_application(expression):
    function, args = expression.uncurry()
    function_str = convert_tptp(function)
    args_str = ','.join(convert_tptp(arg) for arg in args)
    tptp_expr = function_str + Tokens.OPEN + args_str + Tokens.CLOSE
    return tptp_expr

def convert_tptp_equality(expression):
    first = convert_tptp(expression.first)
    second = convert_tptp(expression.second)
    tptp_str = Tokens.OPEN + first + ' = ' + second + Tokens.CLOSE
    return tptp_str

def convert_tptp_and(expression):
    first = convert_tptp(expression.first)
    second = convert_tptp(expression.second)
    tptp_str = Tokens.OPEN + first + ' & ' + second + Tokens.CLOSE
    return tptp_str

def convert_tptp_or(expression):
    first = convert_tptp(expression.first)
    second = convert_tptp(expression.second)
    tptp_str = Tokens.OPEN + first + ' | ' + second + Tokens.CLOSE
    return tptp_str

def convert_tptp_imp(expression):
    first = convert_tptp(expression.first)
    second = convert_tptp(expression.second)
    tptp_str = Tokens.OPEN + first + ' => ' + second + Tokens.CLOSE
    return tptp_str

def convert_tptp_iff(expression):
    first = convert_tptp(expression.first)
    second = convert_tptp(expression.second)
    tptp_str = Tokens.OPEN + first + ' <=> ' + second + Tokens.CLOSE
    return tptp_str

def convert_tptp_not(expression):
    term = convert_tptp(expression.term)
    tptp_str = Tokens.OPEN + "~" + term + Tokens.CLOSE
    return tptp_str

def convert_tptp_exists(expression):
    variable = convert_tptp(expression.variable).upper()
    term = convert_tptp(expression.term)
    tptp_str = '?[' + variable + ']: ' + Tokens.OPEN + term + Tokens.CLOSE
    return tptp_str

def convert_tptp_all(expression):
    variable = convert_tptp(expression.variable).upper()
    term = convert_tptp(expression.term)
    tptp_str = '![' + variable + ']: ' + Tokens.OPEN + term + Tokens.CLOSE
    return tptp_str

def convert_tptp_lambda(expression):
    variable = convert_tptp(expression.variable).upper()
    term = convert_tptp(expression.term)
    tptp_str = '?[' + variable + ']: ' + Tokens.OPEN + term + Tokens.CLOSE
    return tptp_str
