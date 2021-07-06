from os import replace
from nltk.sem.logic import *

class VarStore:
    def __init__(self):
        self.count = 0

    def get(self):
        self.count += 1
        return f'a{(self.count - 1)}'

store = VarStore()

def span_match(span, position, sentence_num):
    return span['start'] <= position and span['end'] > position and span['line_num'] == sentence_num

def main_span(coref_sentence, position, sentence_num):
    for coref in coref_sentence:
        if(span_match(coref['main'], position, sentence_num)):
            return coref['main']
    return None

def mention_span(coref_sentence, position, sentence_num):
    for coref in coref_sentence:
        for mention in coref['mentions']:
            if (span_match(mention, position, sentence_num)):
                return mention
    return None

def span_to_identifier(span):
    text = span['text'].replace(' ', '_')
    return f"__{span['start']}_{span['end']}_{span['line_num']}_{text}"

def replace_main(logic_expr, span, replacements):
    if isinstance(logic_expr, LambdaExpression):
        function_name = ConstantExpression(Variable(span_to_identifier(span)))
        function_arg = IndividualVariableExpression(logic_expr.variable)
        logic_expr.term = AndExpression(ApplicationExpression(function_name, function_arg), logic_expr.term)
    elif isinstance(logic_expr, ConstantExpression):
        original = str(logic_expr.variable)
        new = span_to_identifier(span)
        logic_expr.variable = Variable(new)
        replacements[new] = original
    else:
        raise Exception

def replace_mention(logic_expr, span):
    if isinstance(logic_expr, LambdaExpression):
        function_name = ConstantExpression(Variable(span_to_identifier(span)))
        function_arg = IndividualVariableExpression(logic_expr.term.term.variable)
        logic_expr.term.term.term = AndExpression(ApplicationExpression(function_name, function_arg), logic_expr.term.term.term)
    else:
        raise Exception

def rename_bound_vars(formula):
    if isinstance(formula, ApplicationExpression):
        rename_bound_vars(formula.function)
        rename_bound_vars(formula.argument)
    elif isinstance(formula, VariableBinderExpression):
        rename_bound_vars(formula.term)
        var_name = store.get()
        formula.term = formula.term.replace(formula.variable, IndividualVariableExpression(Variable(var_name)))
        formula.variable = Variable(var_name)
    elif isinstance(formula, NegatedExpression):
        rename_bound_vars(formula.term)
    elif isinstance(formula, BinaryExpression):
        rename_bound_vars(formula.first)
        rename_bound_vars(formula.second)
    return formula

def find_func_arg(formula, func_name):
    if isinstance(formula, ApplicationExpression):
        if(str(formula.function) == func_name):
            return str(formula.argument)
        else:
            func_arg = find_func_arg(formula.function, func_name)
            if func_arg is not None:
                return func_arg
            return find_func_arg(formula.argument, func_name)
    elif isinstance(formula, VariableBinderExpression):
        return find_func_arg(formula.term, func_name)
    elif isinstance(formula, NegatedExpression):
        return find_func_arg(formula.term, func_name)
    elif isinstance(formula, BinaryExpression):
        first_arg = find_func_arg(formula.first, func_name)
        if first_arg is not None:
            return first_arg
        return find_func_arg(formula.second, func_name)
    return None

def replace_with_equality(formula, func_name, eq_var):
    if isinstance(formula, ApplicationExpression):
        if(str(formula.function) == func_name):
            return EqualityExpression(formula.argument, IndividualVariableExpression(Variable(eq_var)))
        else:
            formula.function = replace_with_equality(formula.function, func_name, eq_var)
            formula.argument = replace_with_equality(formula.argument, func_name, eq_var)
    elif isinstance(formula, VariableBinderExpression):
        formula.term = replace_with_equality(formula.term, func_name, eq_var)
    elif isinstance(formula, NegatedExpression):
        formula.term = replace_with_equality(formula.term, func_name, eq_var)
    elif isinstance(formula, BinaryExpression):
        formula.first = replace_with_equality(formula.first, func_name, eq_var)
        formula.second = replace_with_equality(formula.second, func_name, eq_var)
    return formula

def erace_predicate(formula, func_name):
    if isinstance(formula, ApplicationExpression):
        formula.function = erace_predicate(formula.function, func_name)
        formula.argument = erace_predicate(formula.argument, func_name)
    elif isinstance(formula, VariableBinderExpression):
        formula.term = erace_predicate(formula.term, func_name)
    elif isinstance(formula, NegatedExpression):
        formula.term = erace_predicate(formula.term, func_name)
    elif isinstance(formula, BinaryExpression):
        if isinstance(formula.first, ApplicationExpression) and str(formula.first.function) == func_name:
            return formula.second
        elif isinstance(formula.second, ApplicationExpression) and str(formula.second.function) == func_name:
            return formula.first
        formula.first = erace_predicate(formula.first, func_name)
        formula.second = erace_predicate(formula.second, func_name)
    return formula

def replace_const_back(formula, id_old, id_new):
    if isinstance(formula, ApplicationExpression):
        formula.function = replace_const_back(formula.function, id_old, id_new)
        formula.argument = replace_const_back(formula.argument, id_old, id_new)
    elif isinstance(formula, VariableBinderExpression):
        formula.term = replace_const_back(formula.term, id_old, id_new)
    elif isinstance(formula, NegatedExpression):
        formula.term = replace_const_back(formula.term, id_old, id_new)
    elif isinstance(formula, BinaryExpression):
        formula.first = replace_const_back(formula.first, id_old, id_new)
        formula.second = replace_const_back(formula.second, id_old, id_new)
    elif isinstance(formula, ConstantExpression):
        if str(formula) == id_old:
            return ConstantExpression(Variable(id_new))
    return formula

def has_free_occurrence(formula, var):
    if isinstance(formula, ApplicationExpression):
        return has_free_occurrence(formula.function, var) or has_free_occurrence(formula.argument, var)
    elif isinstance(formula, VariableBinderExpression):
        if str(formula.variable) == var:
            return False
        return has_free_occurrence(formula.term, var)
    elif isinstance(formula, NegatedExpression):
        return has_free_occurrence(formula.term, var)
    elif isinstance(formula, BinaryExpression):
        return has_free_occurrence(formula.first, var) or has_free_occurrence(formula.second, var)
    else:
        return str(formula) == var

def pull_out_quantifier(formula):
    if isinstance(formula, ApplicationExpression):
        return formula, False
    elif isinstance(formula, VariableBinderExpression):
        pulled_term, success = pull_out_quantifier(formula.term)
        formula.term = pulled_term
        return formula, success
    elif isinstance(formula, NegatedExpression):
        if isinstance(formula.term, ExistsExpression):
            return AllExpression(formula.variable, NegatedExpression(formula.term)), True
        elif isinstance(formula.term, AllExpression):
            return ExistsExpression(formula.variable, NegatedExpression(formula.term)), True
        else:
            pulled_term, success = pull_out_quantifier(formula.term)
            formula.term = pulled_term
            return formula, success
    elif isinstance(formula, ImpExpression):
        if isinstance(formula.first, AllExpression):
            return ExistsExpression(formula.first.variable, ImpExpression(formula.first.term, formula.second)), True
        elif isinstance(formula.first, ExistsExpression):
            return AllExpression(formula.first.variable, ImpExpression(formula.first.term, formula.second)), True
        elif isinstance(formula.second, AllExpression):
            return AllExpression(formula.second.variable, ImpExpression(formula.first, formula.second.term)), True
        elif isinstance(formula.second, ExistsExpression):
            return ExistsExpression(formula.second.variable, ImpExpression(formula.first, formula.second.term)), True
        else:
            pulled_term, success = pull_out_quantifier(formula.first)
            if success:
                formula.first = pulled_term
                return formula, success
            else:
                pulled_term, success = pull_out_quantifier(formula.second)
                formula.second = pulled_term
                return formula, success
    elif isinstance(formula, AndExpression):
        if isinstance(formula.first, AllExpression):
            return AllExpression(formula.first.variable, AndExpression(formula.first.term, formula.second)), True
        elif isinstance(formula.first, ExistsExpression):
            return ExistsExpression(formula.first.variable, AndExpression(formula.first.term, formula.second)), True
        elif isinstance(formula.second, AllExpression):
            return AllExpression(formula.second.variable, AndExpression(formula.first, formula.second.term)), True
        elif isinstance(formula.second, ExistsExpression):
            return ExistsExpression(formula.second.variable, AndExpression(formula.first, formula.second.term)), True
        else:
            pulled_term, success = pull_out_quantifier(formula.first)
            if success:
                formula.first = pulled_term
                return formula, success
            else:
                pulled_term, success = pull_out_quantifier(formula.second)
                formula.second = pulled_term
                return formula, success
    elif isinstance(formula, OrExpression):
        if isinstance(formula.first, AllExpression):
            return AllExpression(formula.first.variable, OrExpression(formula.first.term, formula.second)), True
        elif isinstance(formula.first, ExistsExpression):
            return ExistsExpression(formula.first.variable, OrExpression(formula.first.term, formula.second)), True
        elif isinstance(formula.second, AllExpression):
            return AllExpression(formula.second.variable, OrExpression(formula.first, formula.second.term)), True
        elif isinstance(formula.second, ExistsExpression):
            return ExistsExpression(formula.second.variable, OrExpression(formula.first, formula.second.term)), True
        else:
            pulled_term, success = pull_out_quantifier(formula.first)
            if success:
                formula.first = pulled_term
                return formula, success
            else:
                pulled_term, success = pull_out_quantifier(formula.second)
                formula.second = pulled_term
                return formula, success
    else:
        return formula, False

def rescope_quantifier(formula, var):
    trial_limit = 500
    for _ in range(trial_limit):
        if not has_free_occurrence(formula, var):
            return formula
        formula, success = pull_out_quantifier(formula)
        if not success:
            return None
    return None

