import pytest
from smt_solver.smt_solver import SMTSolver


class TestSMTSolver:

    @staticmethod
    def test_congruence_closure():
        formula = ('(declare-fun f (Bool Bool) Bool) ' +
                   '(assert (= f(a, b) a)) ' +
                   '(assert (not (= f(f(a, b), b) a)))')
        solver = SMTSolver(formula)
        assert solver._congruence_closure({1: True, 3: False}) == frozenset({3, -1})

        formula = ('(declare-fun f (Bool) Bool) ' +
                   '(assert (= f(f(f(a))) a)) ' +
                   '(assert (= f(f(f(f(f(a))))) a)) ' +
                   '(assert (not (= f(a) a)))')
        solver = SMTSolver(formula)
        assert solver._congruence_closure({1: True, 2: True, 4: False}) == frozenset({4, -1, -2})

        formula = ('(declare-fun f (Bool) Bool) ' +
                   '(assert (= f(x) f(y))) ' +
                   '(assert (not (= x y)))')
        solver = SMTSolver(formula)
        assert solver._congruence_closure({1: True, 3: False}) is None

        formula = ('(declare-fun f (Bool) Bool) ' +
                   '(assert (= f(f(f(a))) a)) ' +
                   '(assert (= f(f(f(f(f(a))))) a)) ' +
                   '(assert (not (= f(a) a)))')
        solver = SMTSolver(formula)
        assert solver._congruence_closure({1: True, 2: True, 4: False}) == frozenset({4, -1, -2})

        formula = ('(declare-fun f (Bool) Bool) ' +
                   '(declare-fun g (Bool) Bool) ' +
                   '(assert (= f(g(x)) g(f(x)))) ' +
                   '(assert (= f(g(f(y))) x)) ' +
                   '(assert (= f(y) x)) ' +
                   '(assert (not (= g(f(x)) x)))')
        solver = SMTSolver(formula)
        assert solver._congruence_closure({1: True, 2: True, 3: True, 5: False}) == frozenset({5, -1, -2, -3})
