import pytest
from smt_solver.smt_solver import SMTSolver


class TestSMTSolver:

    @staticmethod
    def test_congruence_closure():
        formula = ('(declare-fun f (Bool Bool) Bool) ' +
                   '(assert (= f(a, b) a)) ' +
                   '(assert (not (= f(f(a, b), b) a)))')
        solver = SMTSolver(formula)
        solver._solver._assignment = {1: {"value": True}, 3: {"value": False}}
        assert solver._congruence_closure() == frozenset({3, -1})

        formula = ('(declare-fun f (Bool) Bool) ' +
                   '(assert (= f(f(f(a))) a)) ' +
                   '(assert (= f(f(f(f(f(a))))) a)) ' +
                   '(assert (not (= f(a) a)))')
        solver = SMTSolver(formula)
        solver._solver._assignment = {1: {"value": True}, 2: {"value": True}, 4: {"value": False}}
        assert solver._congruence_closure() == frozenset({4, -1, -2})

        formula = ('(declare-fun f (Bool) Bool) ' +
                   '(assert (= f(x) f(y))) ' +
                   '(assert (not (= x y)))')
        solver = SMTSolver(formula)
        solver._solver._assignment = {1: {"value": True}, 3: {"value": False}}
        assert solver._congruence_closure() is None

        formula = ('(declare-fun f (Bool) Bool) ' +
                   '(declare-fun g (Bool) Bool) ' +
                   '(assert (= f(g(x)) g(f(x)))) ' +
                   '(assert (= f(g(f(y))) x)) ' +
                   '(assert (= f(y) x)) ' +
                   '(assert (not (= g(f(x)) x)))')
        solver = SMTSolver(formula)
        solver._solver._assignment = {1: {"value": True}, 2: {"value": True}, 3: {"value": True}, 5: {"value": False}}
        assert solver._congruence_closure() == frozenset({5, -1, -2, -3})
