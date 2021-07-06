from nltk.sem.logic import *

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
        replacements.append([original, new])
    else:
        raise Exception

def replace_mention(logic_expr, span):
    if isinstance(logic_expr, LambdaExpression):
        function_name = ConstantExpression(Variable(span_to_identifier(span)))
        function_arg = IndividualVariableExpression(logic_expr.term.term.variable)
        logic_expr.term.term.term = AndExpression(ApplicationExpression(function_name, function_arg), logic_expr.term.term.term)
    else:
        raise Exception