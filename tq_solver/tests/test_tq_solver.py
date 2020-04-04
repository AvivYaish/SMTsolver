import pytest
from tq_solver.tq_solver import TQSolver
from formula_parser.formula_parser import FormulaParser


class TestTQSolver:
    @staticmethod
    def test_solve():
        assert TQSolver(*FormulaParser.import_tq("(declare-fun x1 () Int) (assert (<= 5x1 1))")).solve()
        assert not TQSolver(*FormulaParser.import_tq("(declare-fun x1 () Int) (assert (<= 5x1 -1))")).solve()

        formula = "(declare-fun x1 () Int) " \
                  "(declare-fun x2 () Int) " \
                  "(declare-fun x3 () Int) " \
                  "(assert (<= (x1 + x2 + 2x3) 4)) " \
                  "(assert (<= (2x1 + 3x3) 5)) " \
                  "(assert (<= (2x1 + x2 + 3x3) 7))"
        assert TQSolver(*FormulaParser.import_tq(formula)).solve()

        formula = "(declare-fun x1 () Int) " \
                  "(assert (and (<= (x1 - x1) 4) (<= (x1) 0))) "
        assert TQSolver(*FormulaParser.import_tq(formula)).solve()

        formula = "(declare-fun x1 () Int) " \
                  "(declare-fun x2 () Int) " \
                  "(assert (and (<= (x2 - x1) 4) (<= (x1) -2))) "
        assert not TQSolver(*FormulaParser.import_tq(formula)).solve()

        formula = "(declare-fun x1 () Int) " \
                  "(declare-fun x2 () Int) " \
                  "(declare-fun x3 () Int) " \
                  "(assert (or (and (<= (x2 -1.1x1) 4) (<= (x1) -2)) (not (<= x3 2.1)))) "
        assert TQSolver(*FormulaParser.import_tq(formula)).solve()

        formula = "(declare-fun x1 () Int) " \
                  "(declare-fun x2 () Int) " \
                  "(declare-fun x3 () Int) " \
                  "(assert (or (and (<= x1 0.1) (not (<= x1 2))) ((<= x3 -0.1)))) "
        assert not TQSolver(*FormulaParser.import_tq(formula)).solve()
