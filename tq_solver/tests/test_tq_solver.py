import pytest
from sat_solver.tests.test_sat_solver import TestSATSolver
from formula_parser.formula_parser import FormulaParser
from tq_solver.tq_solver import TQSolver
import numpy as np
import z3


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

    @staticmethod
    def generate_random_equations(variable_num: int, equation_num: int, coefficient_limits: (int, int)):
        all_variables = list(range(1, variable_num + 1))
        variables_z3, equations_z3 = np.array([z3.Real("x" + str(cur_literal)) for cur_literal in all_variables]), []
        variables_our_txt, equations_our_txt = np.array(["x" + str(cur_literal) for cur_literal in all_variables]), []
        variables_our, equations_our = np.array(["x" + str(cur_literal) for cur_literal in all_variables]), []
        for coefficients in np.random.uniform(*coefficient_limits, size=(equation_num, variable_num + 1)):
            coefficients = coefficients.round(decimals=3)
            cur_subformula_z3 = np.sum(coefficients[:-1] * variables_z3) <= coefficients[-1]
            cur_subformula_our_txt = np.char.add(np.array(coefficients[:-1], dtype=np.str), variables_our_txt)
            equations_z3.append(cur_subformula_z3)
            equations_our_txt.append(FormulaParser.LESS_EQ + " " + FormulaParser.OPEN_ENCLOSE +
                                     FormulaParser.PLUS.join(cur_subformula_our_txt) +
                                     FormulaParser.CLOSE_ENCLOSE + " " + str(coefficients[-1]))
            equations_our.append((FormulaParser.LESS_EQ, tuple(coefficients[:-1]), coefficients[-1]))
        return ([var >= 0 for var in variables_z3], equations_z3), \
            (" ".join("(declare-fun " + var + " () Int)" for var in variables_our_txt), equations_our_txt), \
            equations_our

    @staticmethod
    @pytest.mark.parametrize("variable_num, equation_num, coefficient_limits",
                             [(5, equation_num, (-5, 5)) for equation_num in list(range(1, 50))])
    def test_random_tq_equations(variable_num: int, equation_num: int, coefficient_limits: (int, int)):
        (all_pos_z3, equations_z3), (var_dec_our_txt, equations_our_txt), equations_our = \
            TestTQSolver.generate_random_equations(variable_num, equation_num, coefficient_limits)
        if not equations_z3:
            return
        try:  # Might be the case that the formula is not valid
            formula_z3 = z3.And(z3.And(all_pos_z3), z3.And(equations_z3))
        except z3.Z3Exception:
            return
        formula_our_txt = var_dec_our_txt + ' '.join(["(assert (" + eq + "))" for eq in equations_our_txt])
        print("\n", "Z3 formula: ", formula_z3, "\n", "Our formula: ", formula_our_txt)
        assert TestSATSolver.compare_to_z3(formula_z3, TQSolver(*FormulaParser.import_tq(formula_our_txt)))

    @staticmethod
    @pytest.mark.parametrize("variable_num, equation_num, coefficient_limits, operator_num",
                             [(5, 10, (-5, 5), operator_num) for operator_num in list(range(1, 50))])
    def test_random_tq_formula(variable_num: int, equation_num: int, coefficient_limits: (int, int), operator_num: int):
        (all_pos_z3, equations_z3), (var_dec_our_txt, equations_our_txt), equations_our = \
            TestTQSolver.generate_random_equations(variable_num, equation_num, coefficient_limits)
        if not equations_z3:
            return
        try:  # Might be the case that the formula is not valid
            formula_z3, formula_our_txt, formula_our = \
                TestSATSolver.generate_random_formula(0, operator_num, equations_z3, equations_our_txt, equations_our)
            formula_z3 = z3.And(z3.And(all_pos_z3), formula_z3)
        except z3.Z3Exception:
            return
        formula_our_txt = var_dec_our_txt + ' '.join(["(assert (" + formula + "))" for formula in formula_our_txt])
        print("\n", "Z3 formula: ", formula_z3, "\n", "Our formula: ", formula_our_txt)
        assert TestSATSolver.compare_to_z3(formula_z3, TQSolver(*FormulaParser.import_tq(formula_our_txt)))
