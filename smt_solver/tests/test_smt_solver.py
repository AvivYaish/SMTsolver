import pytest
from formula_parser.formula_parser import FormulaParser
from smt_solver.smt_solver import SMTSolver


class TestSMTSolver:

    @staticmethod
    def test_congruence_closure():
        formula = ('(declare-fun f (Bool) Bool) ' +
                   '(assert (= f(f(f(a))) a)) ' +
                   '(assert (= f(f(f(f(f(a))))) a)) ' +
                   '(assert (not (= f(a) a)))')
        solver = SMTSolver(formula)
        assert not solver._congruence_closure({1: True, 2: True, 4: False})
