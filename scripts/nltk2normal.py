# -*- coding: utf-8 -*-

from nltk.sem.logic import *
import unicodedata

from nltk.internals import Counter
from logic_parser import lexpr

_counter = Counter()

# Term t ::=
#   x,y,z         <IndividualVariableExpression>
#   e             <EventVariableExpression>
#   f(t)          <ApplicationExpression> where f in {Subj,Obj,Dat,...}
#   john          <ConstantExpression>
#   \x.student(x) <LambdaExpression>

# Formula A ::=
#   F(t)         <ApplicationExpression>
#   F(t,u)       <ApplicationExpression>
#   t = u        <EqualityExpression>
#   A & B        <AndExpression>
#   A | B        <OrExpression>
#   A -> B       <ImpExpression>
#   -A           <NegatedExpression>
#   exists x.A   <ExistsExpression>
#   forall x.A   <AllExpression>
#   True         <ConstantExpression>

def get_atomic_formulas(expression):
    if isinstance(expression, ApplicationExpression):
        return set([expression])
    elif isinstance(expression, EqualityExpression):
        return set([expression])
    elif isinstance(expression, AbstractVariableExpression):
        return set([expression])
    else:
        return expression.visit(get_atomic_formulas,
                       lambda parts: reduce(operator.or_, parts, set()))

def get_role_formulas(expression):
    if isinstance(expression, EqualityExpression):
        if isinstance(expression.first, ApplicationExpression):
            variable = expression.first.argument
            if isinstance(variable, EventVariableExpression):
                return set([expression])
            else:
                return set()
        else:
            return set()
    elif isinstance(expression, AbstractVariableExpression):
        return set()
    else:
        return expression.visit(get_role_formulas,
                       lambda parts: reduce(operator.or_, parts, set()))

def new_variable(var):
    var = VariableExpression(var)
    # isinstance(var,EventVariableExpression) must come first
    if isinstance(var, EventVariableExpression):
        prefix = 'e0'
    elif isinstance(var, IndividualVariableExpression):
        prefix = 'x0'
    elif isinstance(var, FunctionVariableExpression):
        prefix = 'F0'
    else:
        prefix = 'z0'
    v = Variable("%s%s" % (prefix, _counter.get()))
    return v

true_preds = ['True', 'TrueP']

def remove_true(expression):
    # Remove True and TrueP
    if isinstance(expression, ApplicationExpression):
        function = remove_true(expression.function)
        argument = remove_true(expression.argument)
        expr = ApplicationExpression(function, argument)
    elif isinstance(expression, EqualityExpression):
        left = remove_true(expression.first)
        right = remove_true(expression.second)
        expr = EqualityExpression(left, right)
    elif isinstance(expression, AndExpression):
        # True & A <=> A & True <=> A
        left = expression.first
        right = expression.second
        left_str = str(left)
        right_str = str(right)
        if left_str in true_preds:
            expr = remove_true(right)
        elif right_str in true_preds:
            expr = remove_true(left)
        else:
            left = remove_true(left)
            right = remove_true(right)
            expr = AndExpression(left, right)
    elif isinstance(expression, OrExpression):
        # True or A <=> A or True <=> True
        left = expression.first
        right = expression.second
        left_str = str(left)
        right_str = str(right)
        if left_str in true_preds:
            expr = remove_true(left)
        elif right_str in true_preds:
            expr = remove_true(right)
        else:
            left = remove_true(left)
            right = remove_true(right)
            expr = OrExpression(left, right)
    elif isinstance(expression, ImpExpression):
        # True -> A <=> A
        left = expression.first
        right = expression.second
        left_str = str(left)
        if left_str in true_preds:
            expr = remove_true(right)
        else:
            left = remove_true(expression.first)
            right = remove_true(expression.second)
            expr = ImpExpression(left, right)
    elif isinstance(expression, NegatedExpression):
        term = remove_true(expression.term)
        expr = NegatedExpression(term)
    elif isinstance(expression, ExistsExpression):
        variable = expression.variable
        term = expression.term
        term = remove_true(term)
        expr = ExistsExpression(variable, term)
    elif isinstance(expression, AllExpression):
        variable = expression.variable
        term = expression.term
        term = remove_true(term)
        expr = AllExpression(variable, term)
    elif isinstance(expression, LambdaExpression):
        variable = expression.variable
        term = expression.term
        term = remove_true(term)
        expr = LambdaExpression(variable, term)
    else:
        expr = expression
    return expr

def remove_true_(expression):
    # Remove True and TrueP
    if isinstance(expression, ApplicationExpression):
        function = remove_true(expression.function)
        argument = remove_true(expression.argument)
        expr = ApplicationExpression(function, argument)
    elif isinstance(expression, EqualityExpression):
        left = remove_true(expression.first)
        right = remove_true(expression.second)
        expr = EqualityExpression(left, right)
    elif isinstance(expression, AndExpression):
        # True & A <=> A & True <=> A
        left = expression.first
        right = expression.second
        left_str = str(left)
        right_str = str(right)
        if left_str in true_preds:
            expr = remove_true(right)
        elif right_str in true_preds:
            expr = remove_true(left)
        else:
            left = remove_true(left)
            right = remove_true(right)
            expr = AndExpression(left, right)
    elif isinstance(expression, OrExpression):
        # True or A <=> A or True <=> True
        left = expression.first
        right = expression.second
        left_str = str(left)
        right_str = str(right)
        if left_str in true_preds:
            expr = remove_true(left)
        elif right_str in true_preds:
            expr = remove_true(right)
        else:
            left = remove_true(left)
            right = remove_true(right)
            expr = OrExpression(left, right)
    elif isinstance(expression, ImpExpression):
        # True -> A <=> A
        left = expression.first
        right = expression.second
        left_str = str(left)
        if left_str in true_preds:
            expr = remove_true(right)
        else:
            left = remove_true(expression.first)
            right = remove_true(expression.second)
            expr = ImpExpression(left, right)
    elif isinstance(expression, NegatedExpression):
        term = remove_true(expression.term)
        expr = NegatedExpression(term)
    elif isinstance(expression, ExistsExpression):
        variable = expression.variable
        term = expression.term
        newvar = new_variable(variable)
        newvar_expr = VariableExpression(newvar)
        term = term.replace(variable, newvar_expr)
        term = remove_true(term)
        expr = ExistsExpression(newvar, term)
    elif isinstance(expression, AllExpression):
        variable = expression.variable
        term = expression.term
        newvar = new_variable(variable)
        newvar_expr = VariableExpression(newvar)
        term = term.replace(variable, newvar_expr)
        term = remove_true(term)
        expr = AllExpression(newvar, term)
    elif isinstance(expression, LambdaExpression):
        variable = expression.variable
        term = expression.term
        newvar = new_variable(variable)
        newvar_expr = VariableExpression(newvar)
        term = term.replace(variable, newvar_expr)
        term = remove_true(term)
        expr = LambdaExpression(newvar, term)
    # elif isinstance(expression, IndividualVariableExpression):
    #     expr = expression
    # elif isinstance(expression, EventVariableExpression):
    #     expr = expression
    # elif isinstance(expression, FunctionVariableExpression):
    #     expr = expression
    # elif isinstance(expression, ConstantExpression):
    #     expr = expression
    else:
        expr = expression
    return expr

def rename_variable(expression):
    # Rename bound variables so that no variable with the same name is bound
    # by two different quantifiers in different parts of a formula
    if isinstance(expression, ApplicationExpression):
        function = rename_variable(expression.function)
        argument = rename_variable(expression.argument)
        expr = ApplicationExpression(function, argument)
    elif isinstance(expression, EqualityExpression):
        left = rename_variable(expression.first)
        right = rename_variable(expression.second)
        expr = EqualityExpression(left, right)
    elif isinstance(expression, AndExpression):
        left = rename_variable(expression.first)
        right = rename_variable(expression.second)
        expr = AndExpression(left, right)
    elif isinstance(expression, OrExpression):
        left = rename_variable(expression.first)
        right = rename_variable(expression.second)
        expr = OrExpression(left, right)
    elif isinstance(expression, ImpExpression):
        left = rename_variable(expression.first)
        right = rename_variable(expression.second)
        expr = ImpExpression(left, right)
    elif isinstance(expression, NegatedExpression):
        term = rename_variable(expression.term)
        expr = NegatedExpression(term)
    elif isinstance(expression, ExistsExpression):
        variable = expression.variable
        term = expression.term
        newvar = new_variable(variable)
        newvar_expr = VariableExpression(newvar)
        term = term.replace(variable, newvar_expr)
        term = rename_variable(term)
        expr = ExistsExpression(newvar, term)
    elif isinstance(expression, AllExpression):
        variable = expression.variable
        term = expression.term
        newvar = new_variable(variable)
        newvar_expr = VariableExpression(newvar)
        term = term.replace(variable, newvar_expr)
        term = rename_variable(term)
        expr = AllExpression(newvar, term)
    elif isinstance(expression, LambdaExpression):
        variable = expression.variable
        term = expression.term
        newvar = new_variable(variable)
        newvar_expr = VariableExpression(newvar)
        term = term.replace(variable, newvar_expr)
        term = rename_variable(term)
        expr = LambdaExpression(newvar, term)
    # elif isinstance(expression, IndividualVariableExpression):
    #     expr = expression
    # elif isinstance(expression, EventVariableExpression):
    #     expr = expression
    # elif isinstance(expression, FunctionVariableExpression):
    #     expr = expression
    # elif isinstance(expression, ConstantExpression):
    #     expr = expression
    else:
        expr = expression
    return expr

def convert_to_prenex(expression):
    # Convert a formula to one where all existential quantifers come first.
    expression = remove_true(expression)
    expression = rename_variable(expression)
    prenex_form = prenex_expr(expression)
    return prenex_form

def prenex_expr(expression):
    if isinstance(expression, ApplicationExpression):
        expr = prenex_application_expr(expression)
    elif isinstance(expression, EqualityExpression):
        expr = prenex_equality_expr(expression)
    elif isinstance(expression, AndExpression):
        expr = prenex_and_expr(expression)
    elif isinstance(expression, OrExpression):
        expr = prenex_or_expr(expression)
    elif isinstance(expression, ImpExpression):
        expr = prenex_imp_expr(expression)
    elif isinstance(expression, NegatedExpression):
        expr = prenex_not_expr(expression)
    elif isinstance(expression, ExistsExpression):
        expr = prenex_exists_expr(expression)
    elif isinstance(expression, AllExpression):
        expr = prenex_all_expr(expression)
    elif isinstance(expression, LambdaExpression):
        expr = prenex_lambda_expr(expression)
    elif isinstance(expression, IndividualVariableExpression):
        expr = expression
    elif isinstance(expression, EventVariableExpression):
        expr = expression
    elif isinstance(expression, ConstantExpression):
        lexstr = normalize_symbols('%s' % expression)
        expr = ConstantExpression(Variable(lexstr))
    # elif isinstance(expression, Variable):
    #     expr = expression
    else:
        expr = expression
    return expr

def prenex_application_expr(expression):
    function = prenex_expr(expression.function)
    argument = prenex_expr(expression.argument)
    expr = ApplicationExpression(function, argument)
    return expr

def prenex_equality_expr(expression):
    left = prenex_expr(expression.first)
    right = prenex_expr(expression.second)
    expr = EqualityExpression(left, right)
    return expr

def prenex_and_expr(expression):
    left = prenex_expr(expression.first)
    right = prenex_expr(expression.second)
    # [(exists x. L) & R] = exists x. [L & R]
    if isinstance(left, ExistsExpression):
        left_variable = left.variable
        left_term = left.term
        if not left_variable in right.free():
            body = prenex_expr(AndExpression(left_term, right))
            expr = ExistsExpression(left_variable, body)
        else:
            newvar = unique_variable()
            var = VariableExpression(newvar)
            left_term = left_term.replace(left_variable, var)
            body = prenex_expr(AndExpression(left_term, right))
            expr = ExistsExpression(newvar, body)
    # [L & (exists x. R)] = exists x. [L & R]
    elif isinstance(right, ExistsExpression):
        right_variable = right.variable
        right_term = right.term
        if not right_variable in left.free():
            body = prenex_expr(AndExpression(left, right_term))
            expr = ExistsExpression(right_variable, body)
        else:
            newvar = unique_variable()
            var = VariableExpression(newvar)
            right_term = right_term.replace(right_variable, var)
            body = prenex_expr(AndExpression(left, right_term))
            expr = ExistsExpression(newvar, body)
    else:
        expr = AndExpression(left, right)
    return expr

def prenex_or_expr(expression):
    left = prenex_expr(expression.first)
    right = prenex_expr(expression.second)
    expr = OrExpression(left, right)
    return expr

def prenex_imp_expr(expression):
    left = prenex_expr(expression.first)
    right = prenex_expr(expression.second)
    expr = ImpExpression(left, right)
    return expr

def prenex_not_expr(expression):
    term = prenex_expr(expression.term)
    expr = NegatedExpression(term)
    return expr

def prenex_exists_expr(expression):
    variable = expression.variable
    term = prenex_expr(expression.term)
    expr = ExistsExpression(variable, term)
    return expr

def prenex_all_expr(expression):
    variable = expression.variable
    term = prenex_expr(expression.term)
    expr = AllExpression(variable, term)
    return expr

def prenex_lambda_expr(expression):
    variable = expression.variable
    term = prenex_expr(expression.term)
    expr = LambdaExpression(variable, term)
    return expr

def normalize_symbols(expression):
  expression = expression.replace("’","").\
               replace("_","").\
               replace("（","BracketLeft").\
               replace("）","BracketRight")
  expression = unicodedata.normalize('NFKC', expression)
  return expression


# Examples
v1 = lexpr(r'x')
v2 = lexpr(r'x1')
v3 = lexpr(r'e1')
v4 = lexpr(r'z1')
v5 = lexpr(r'y')

atom1 = lexpr(r'_student(z1)')
atom2 = lexpr(r'_student(x,z1)')
atom3 = lexpr(r'(x = z1)')
atom4 = lexpr(r'_run(Subj(x))')
atom5 = lexpr(r'(Subj(x) = y)')

nonatom1 = lexpr(r'\x.\y.sees(x,y)(john)(mary)')
nonatom2 = lexpr(r'\x.sees(x,y)(john)')

and1 = lexpr(r'_student(z1) & _run(z1)')
and2 = lexpr(r'_student(z1) & _run(z1) & _boy(y)')
and3 = lexpr(r'_student(z1) & (x = z1)')

or1 = lexpr(r'_student(z1) | _run(z1)')
or2 = lexpr(r'(_student(z1) | _run(z1)) & _boy(y)')
or3 = lexpr(r'_student(z1) | (x = z1)')

imp1 = lexpr(r'_student(z1) -> _run(z1)')
imp2 = lexpr(r'(_student(z1) & _run(z1)) -> _boy(y)')
imp3 = lexpr(r'_student(z1) -> (x = z1)')

neg1 = lexpr(r'- _student(z1)')
neg2 = lexpr(r'- (_student(z1) & _run(z1))')
neg3 = lexpr(r'_student(z1) & - (x = z1)')

ex1 = lexpr(r'exists z1.(_student(z1) & _run(z1))')
ex2 = lexpr(r'exists z1.(_student(z1) & _run(z1) & exists x.(boy(x) & like(z1,x)))')
ex3 = lexpr(r'exists x z1.(_student(z1) & _run(z1) & boy(x) & like(z1,x))')
ex4 = lexpr(r'exists e x.(_run(z1) & boy(x) & like(z1,x))')
ex5 = lexpr(r'exists e x.(_run(e) & boy(x) & (Subj(e) = x))')
ex6 = lexpr(r'exists z1.(_student(z1) & exists x.(boy(x) & like(z1,x)))')
ex7 = lexpr(r'exists e.(_come(e) & (Subj(e) = x) & exists x.(_party(x) & _to(e,x)))')
ex8 = lexpr(r'exists e z1.(_come(z1) & (Subj(e) = z1) & exists z1.(_party(z1) & _to(e,z1)))')
ex9 = lexpr(r'exists e y.(_run(e) & boy(y) & (Subj(e) = y)) & exists e y.(_run(e) & boy(y) & (Subj(e) = y))')
ex10 = lexpr(r'exists e1 e2 x1 (_run(e1) & _walk(e2) & (Subj(e1) = x1) & (Subj(e2) = x1) & _boy(x1))')
ex11 = lexpr(r'exists e1 e2 x1 (_歩く(e1) & _走る(e2) & (Subj(e1) = x1) & (Subj(e2) = x1) & _男の子(x1))')

all1 = lexpr(r'forall x. (_student(x))')
all2 = lexpr(r'forall x. (_student(x) -> _run(x))')
all3 = lexpr(r'all x.(_student(x) -> exists e.(_come(e) & (Subj(e) = x) & exists x.(_party(x) & _to(e,x))))')

tr1 = lexpr(r'True')
tr2 = lexpr(r'True & (x = z1)')
tr3 = lexpr(r'_student(z1) & True & (x = z1)')

lam1 = lexpr(r'\x._student(x)')
lam2 = lexpr(r'know(john,\x._student(x))')
lam3 = lexpr(r'\x.\y.sees(x,y)(john)(mary)')
lam4 = lexpr(r'\x.\y.sees(x,y)(john, mary)')
lam5 = lexpr(r'all x.(man(x) & (\x.exists y.walks(x,y))(x))')
lam6 = lexpr(r'(\P.\Q.exists x.(P(x) & Q(x)))(\x.dog(x))(\x.bark(x))')

comp1 = lexpr(r'exists x.(_john(x) & True & exists z1.(_student(z1) & True & (x = z1)))')
comp2 = lexpr(r'exists x.(_john(x) & True & exists e.(_come(e) & (Subj(e) = x) & exists x.(_party(x) & True & _to(e,x) & True)))')
comp3 = lexpr(r'all x.(_student(x) -> (True -> exists e.(_come(e) & (Subj(e) = x) & exists x.(_party(x) & True & _to(e,x) & True))))')
comp4 = lexpr(r'exists x.(_john(x) & True & exists z1.(_student(z1) & True & (x = z1)) & exists x.(_walk(x) & _with(x,z1)))')
comp5 = lexpr(r'exists x.(_john(x) & forall z1.(_student(z1) & rel(x,z1)))')
comp6 = lexpr(r'(exists x.(_boy(x) & True & exists e.(_walk(e) & (Subj(e) = x) & True)) & exists x.(_girl(x) & True & exists e.(_walk(e) & (Subj(e) = x) & True)))')
comp7 = lexpr(r'(exists x.(_john(x) & True & exists z1.(_coffee(z1) & True & exists e.(_drink(e) & (Subj(e) = x) & (Acc(e) = z1) & True))) & exists x.(_bob(x) & True & exists z1.(_coffee(z1) & True & exists e.(_drink(e) & (Subj(e) = x) & (Acc(e) = z1) & True))))')
comp8 = lexpr(r'(exists x.(_boy(x) & True & exists z1.(_coffee(z1) & True & exists e.(_drink(e) & (Subj(e) = x) & (Acc(e) = z1) & True)) & exists z2.(_guitar(z2) & True & exists e.(_play(e) & (Subj(e) = x) & (Acc(e) = z2) & True))) & exists x.(_girl(x) & True & exists z1.(_coffee(z1) & True & exists e.(_drink(e) & (Subj(e) = x) & (Acc(e) = z1) & True)) & exists z2.(_guitar(z2) & True & exists e.(_play(e) & (Subj(e) = x) & (Acc(e) = z2) & True))))')
comp9 = lexpr(r'(exists x.(_boy(x) & True & exists e.(_walk(e) & (Subj(e) = x) & exists x.(_park(x) & True & _in(e,x) & True))) & exists x.(_girl(x) & True & exists e.(_walk(e) & (Subj(e) = x) & exists x.(_park(x) & True & _in(e,x) & True))))')
comp10 = lexpr(r'(exists x.(_john(x) & True & exists e.(_move(e) & (Subj(e) = x) & exists x.(_tokyo(x) & True & _from(e,x) & exists x.(_paris(x) & True & _to(e,x) & True)))) & exists x.(_bob(x) & True & exists e.(_move(e) & (Subj(e) = x) & exists x.(_tokyo(x) & True & _from(e,x) & exists x.(_paris(x) & True & _to(e,x) & True)))))')
comp11 = lexpr(r'(exists x.(_boy(x) & True & exists e.(_walk(e) & (Subj(e) = x) & _slowly(e) & True)) & exists x.(_girl(x) & True & exists e.(_walk(e) & (Subj(e) = x) & _slowly(e) & True)))')
comp12 = lexpr(r'(exists x.(_boy(x) & True & exists e.(_walk(e) & (Subj(e) = x) & _slowly(e) & exists x.(_park(x) & True & _in(e,x) & True))) & exists x.(_girl(x) & True & exists e.(_walk(e) & (Subj(e) = x) & _slowly(e) & exists x.(_park(x) & True & _in(e,x) & True))))')
comp13 = lexpr(r'exists x.(_walking(x) & _man(x) & True & exists e.((Subj(e) = Subj(e)) & True))')


test = [v1,v2,v3,
        atom1,atom2,atom3,atom4,atom5,
        nonatom1,nonatom2,
        and1,and2,and3,
        or1,or2,or3,
        imp1,imp2,imp3,
        neg1,neg2,neg3,
        ex1,ex2,ex3,ex4,ex5,ex6,ex7,ex8,ex9,
        all1,all2,all3,
        tr1,tr2,tr3,
        lam1,lam2,lam3,lam4,lam5,lam6,
        comp1,comp2,comp3,comp4,comp5,comp6,comp7,comp8,comp9,comp10,comp11,comp12,comp13]

def demo(function):
    for formula in test:
        answer = function(formula)
        print('Formula: {0}'.format(formula))
        print('Prediction: {0}\n'.format(answer))
