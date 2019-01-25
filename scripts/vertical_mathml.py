# -*- coding: utf-8 -*-

from nltk.sem.logic import *
from logic_parser import lexpr

kSize = 1.0
kColor = 'Black'

def basic_exp(expression):
    if str(expression)[0] == '_':
         str_expression = str(expression)[1:]
    else:
         str_expression = str(expression)
    return "<mtext" \
           + " fontsize='" + str(kSize) + "'" \
           + " color='" + kColor + "'>" \
           + str_expression \
           + "</mtext>\n"

def convert_to_vertical(expression):
    if isinstance(expression, str):
        expression = lexpr(expression)
    expr_vertical_str = ''
    if isinstance(expression, ApplicationExpression):
        args = expression.args
        if str(expression.pred) == 'lt':
            first_arg = convert_to_vertical(args[0])
            second_arg = convert_to_vertical(args[1])
            expr_vertical_str = first_arg \
                           + '<mspace width=".1em"/>' \
                           + '<mtext>&lt;</mtext>' \
                           + '<mspace width=".1em"/>' \
                           + second_arg
        elif str(expression.pred) == 'le':
            first_arg = convert_to_vertical(args[0])
            second_arg = convert_to_vertical(args[1])
            expr_vertical_str = first_arg \
                           + '<mspace width=".1em"/>' \
                           + '<mtext>&le;</mtext>' \
                           + '<mspace width=".1em"/>' \
                           + second_arg
        else:
            function = convert_to_vertical(expression.pred)
            args_str = [convert_to_vertical(arg) for arg in args]
            args_str = '<mtext>,</mtext><mspace width=".1em"/>'.join(args_str)
            expr_vertical_str = function \
                           + "<mtext>(</mtext>" \
                           + args_str \
                           + "<mtext>)</mtext>\n"
    elif isinstance(expression, LambdaExpression):
        binding_variable = str(expression.variable)
        body = convert_to_vertical(expression.term)
        expr_vertical_str = "<mtext" \
                       + " fontsize='" + str(kSize) + "'" \
                       + " color='" + kColor + "'>" \
                       + "&lambda;" \
                       + binding_variable \
                       + "." \
                       + "</mtext>" \
                       + "<mspace width='.1em'/>\n" \
                       + body
    elif isinstance(expression, ExistsExpression):
        binding_variable = str(expression.variable)
        body = convert_to_vertical(expression.term)
        if binding_variable[0] == 'v':
            var_type = 'Event'
        if binding_variable[0] == 'e':
            var_type = 'Event'
        elif binding_variable[0] == 'g':
            var_type = 'Entity &rarr; Prop'
        else:
            var_type = 'Entity'
        expr_vertical_str = "<mfenced open='[' close=']'>\n" \
                       + "  <mtable columnalign='left'>" \
                       + "    <mtr>\n" \
                       + "      <mtd>\n" \
                       + "      <mtext" \
                       + " fontsize='" + str(kSize) + "'" \
                       + " color='" + kColor + "'>" \
                       + binding_variable \
                       + ":" + var_type \
                       + "      </mtext>\n" \
                       + "      </mtd>\n" \
                       + "    </mtr>\n" \
                       + "    <mtr>\n" \
                       + "      <mtd>\n" \
                       + body \
                       + "      </mtd>\n" \
                       + "    </mtr>\n" \
                       + "  </mtable>\n" \
                       + "</mfenced>\n"
    elif isinstance(expression, AllExpression):
        binding_variable = str(expression.variable)
        body = convert_to_vertical(expression.term)
        if binding_variable[0] == 'v':
            var_type = 'Event'
        if binding_variable[0] == 'e':
            var_type = 'Event'
        elif binding_variable[0] == 'g':
            var_type = 'Entity &rarr; Prop'
        else:
            var_type = 'Entity'
        expr_vertical_str = "<mtext" \
                       + " fontsize='" + str(kSize) + "'" \
                       + " color='" + kColor + "'>" \
                       + "(" \
                       + binding_variable \
                       + ":" + var_type \
                       + ")" \
                       + "</mtext>\n" \
                       + "<mo> &rarr; </mo>\n" \
                       + body
    elif isinstance(expression, AndExpression):
        left = convert_to_vertical(expression.first)
        right = convert_to_vertical(expression.second)
        expr_vertical_str = "<mfenced open='[' close=']'>\n" \
                       + "  <mtable columnalign='left'>\n" \
                       + "    <mtr>\n" \
                       + "      <mtd>\n" \
                       + left \
                       + "      </mtd>\n" \
                       + "    </mtr>\n" \
                       + "    <mtr>\n" \
                       + "      <mtd>\n" \
                       + right \
                       + "      </mtd>\n" \
                       + "    </mtr>\n" \
                       + "  </mtable>\n" \
                       + "</mfenced>\n"
    elif isinstance(expression, OrExpression):
        left = convert_to_vertical(expression.first)
        right = convert_to_vertical(expression.second)
        expr_vertical_str = left \
                       + "<mspace width='.1em'/>" \
                       + "<mo> &or; </mo>\n" \
                       + "<mspace width='.1em'/>" \
                       + right
    elif isinstance(expression, ImpExpression):
        left = convert_to_vertical(expression.first)
        right = convert_to_vertical(expression.second)
        expr_vertical_str = left \
                       + "<mspace width='.1em'/>" \
                       + "<mo> &rarr; </mo>\n" \
                       + "<mspace width='.1em'/>" \
                       + right
    elif isinstance(expression, NegatedExpression):
        body = convert_to_vertical(expression.term)
        expr_vertical_str = "<mo> &not; </mo>\n" \
                       + body
    elif isinstance(expression, EqualityExpression):
        left = convert_to_vertical(expression.first)
        right = convert_to_vertical(expression.second)
        expr_vertical_str = left \
                       + "<mspace width='.1em'/>" \
                       + "<mo> = </mo>\n" \
                       + "<mspace width='.1em'/>" \
                       + right
    elif isinstance(expression, ConstantExpression):
        expr_vertical_str = basic_exp(expression)
    elif isinstance(expression, IndividualVariableExpression):
        expr_vertical_str = basic_exp(expression)
    elif isinstance(expression, FunctionVariableExpression):
        expr_vertical_str = basic_exp(expression)
    else:
        expr_vertical_str = basic_exp(expression)
    return expr_vertical_str
