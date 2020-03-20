import pytest
from formula_parser.formula_parser import FormulaParser
from smt_solver.smt_solver import SMTSolver


class TestSMTSolver:

    @staticmethod
    def test_create_boolean_abstraction():
        formula = '   ((     (   and (   a   ) (   b   )   ))   )    '
        abstraction = {}
        signature = {}
        parsed_formula = FormulaParser.parse_formula(formula)
        abstracted_formula = SMTSolver._create_boolean_abstraction(parsed_formula, signature, abstraction)
        assert abstracted_formula == ('and', '1', '2')
        assert abstraction == {'a': 1, 'b': 2}

        formula = '(((and (   =     true     false    ) (a))))'
        abstraction = {}
        parsed_formula = FormulaParser.parse_formula(formula)
        abstracted_formula = SMTSolver._create_boolean_abstraction(parsed_formula, signature, abstraction)
        assert abstracted_formula == ('and', '1', '2')
        assert abstraction == {('=', 'true', 'false'): 1, 'a': 2}

        formula = '(declare-fun f (Int Int) Bool) (assert ((and (= (not a) f ( 1 , 2 ) ) (a))))'
        abstraction = {}
        signature, parsed_formula = FormulaParser.parse_uf(formula)
        abstracted_formula = SMTSolver._create_boolean_abstraction(parsed_formula.pop(), signature, abstraction)
        assert abstracted_formula == ('and', '1', '2')
        assert abstraction == {'a': 2, ('=', ('not', 'a'), ('f', '1', '2')): 1}

        formula = ('(declare-fun f (Int) Bool) ' +
                   '(declare-fun g (Int) Bool) '
                   '(assert (and (and (= g(a) c) (or (not (= f(g(a)) f(c))) (= g(a) d))) (not (= c d)))')
        abstraction = {}
        signature, parsed_formula = FormulaParser.parse_uf(formula)
        abstracted_formula = SMTSolver._create_boolean_abstraction(parsed_formula.pop(), signature, abstraction)
        assert abstracted_formula == ('and', ('and', '1', ('or', ('not', '2'), '3')), ('not', '4'))
        assert abstraction == {('=', ('f', ('g', 'a')), ('f', 'c')): 2,
                               ('=', ('g', 'a'), 'c'): 1,
                               ('=', ('g', 'a'), 'd'): 3,
                               ('=', 'c', 'd'): 4}
