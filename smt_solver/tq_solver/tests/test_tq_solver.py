import pytest
from smt_solver.sat_solver.tests.test_sat_solver import TestSATSolver
from smt_solver.formula_parser.formula_parser import FormulaParser
from smt_solver.tq_solver.tq_solver import TQSolver
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
                             [(5, equation_num, (-5, 5)) for equation_num in list(range(1, 25)) * 50])
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
    def generate_random_tq_formula(variable_num: int, equation_num: int, coefficient_limits: (int, int),
                                   operator_num: int):
        (all_pos_z3, equations_z3), (var_dec_our_txt, equations_our_txt), equations_our = \
            TestTQSolver.generate_random_equations(variable_num, equation_num, coefficient_limits)
        if not equations_z3:
            return None, None
        try:  # Might be the case that the formula is not valid
            formula_z3, formula_our_txt, formula_our = \
                TestSATSolver.generate_random_formula(0, operator_num, equations_z3, equations_our_txt, equations_our)
            formula_z3 = z3.And(z3.And(all_pos_z3), formula_z3)
        except z3.Z3Exception:
            return None, None
        formula_our = var_dec_our_txt + " (assert (" + formula_our_txt + "))"
        return formula_z3, formula_our

    @staticmethod
    @pytest.mark.parametrize("variable_num, equation_num, coefficient_limits, operator_num",
                             [(5, 10, (-5, 5), operator_num) for operator_num in list(range(1, 50))])
    def test_random_tq_formula(variable_num: int, equation_num: int, coefficient_limits: (int, int), operator_num: int):
        formula_z3, formula_our = TestTQSolver.generate_random_tq_formula(variable_num, equation_num,
                                                                          coefficient_limits, operator_num)
        if formula_z3 is None:
            return
        print("\n", "Z3 formula: ", formula_z3, "\n", "Our formula: ", formula_our)
        assert TestSATSolver.compare_to_z3(formula_z3, TQSolver(*FormulaParser.import_tq(formula_our)))

    @staticmethod
    def test_bad():
        """
Z3 formula:  And(And(x1 >= 0, x2 >= 0, x3 >= 0, x4 >= 0, x5 >= 0),
    Not((-4943/1000*x1 +
         -13/250*x2 +
         -947/1000*x3 +
         -1763/1000*x4 +
         169/500*x5 <=
         4269/1000) ==
        Or(And(159/50*x1 +
               -2269/1000*x2 +
               -453/100*x3 +
               -4967/1000*x4 +
               -546/125*x5 <=
               169/125,
               And(159/50*x1 +
                   -2269/1000*x2 +
                   -453/100*x3 +
                   -4967/1000*x4 +
                   -546/125*x5 <=
                   169/125,
                   4837/1000*x1 +
                   -1957/500*x2 +
                   1173/250*x3 +
                   757/200*x4 +
                   -3853/1000*x5 <=
                   4433/1000)),
           Implies(And(159/50*x1 +
                       -2269/1000*x2 +
                       -453/100*x3 +
                       -4967/1000*x4 +
                       -546/125*x5 <=
                       169/125,
                       4837/1000*x1 +
                       -1957/500*x2 +
                       1173/250*x3 +
                       757/200*x4 +
                       -3853/1000*x5 <=
                       4433/1000),
                   1103/250*x1 +
                   1187/500*x2 +
                   386/125*x3 +
                   -264/125*x4 +
                   -1511/500*x5 <=
                   -2403/500))))
 Our formula:  (declare-fun x1 () Int) (declare-fun x2 () Int) (declare-fun x3 () Int) (declare-fun x4 () Int) (declare-fun x5 () Int) (assert (not (<=> (<= (-4.943x1+-0.052x2+-0.947x3+-1.763x4+0.338x5) 4.269) (or (and (<= (3.18x1+-2.269x2+-4.53x3+-4.967x4+-4.368x5) 1.352) (and (<= (3.18x1+-2.269x2+-4.53x3+-4.967x4+-4.368x5) 1.352) (<= (4.837x1+-3.914x2+4.692x3+3.785x4+-3.853x5) 4.433))) (=> (and (<= (3.18x1+-2.269x2+-4.53x3+-4.967x4+-4.368x5) 1.352) (<= (4.837x1+-3.914x2+4.692x3+3.785x4+-3.853x5) 4.433)) (<= (4.412x1+2.374x2+3.088x3+-2.112x4+-3.022x5) -4.806))))))

 Is SAT? True
 Z3:		 0.021941423416137695
 Our:	 0.003988027572631836
        """
        formula_our = "(declare-fun x1 () Int) (declare-fun x2 () Int) (declare-fun x3 () Int) (declare-fun x4 () Int) (declare-fun x5 () Int) (assert (not (<=> (<= (-4.943x1+-0.052x2+-0.947x3+-1.763x4+0.338x5) 4.269) (or (and (<= (3.18x1+-2.269x2+-4.53x3+-4.967x4+-4.368x5) 1.352) (and (<= (3.18x1+-2.269x2+-4.53x3+-4.967x4+-4.368x5) 1.352) (<= (4.837x1+-3.914x2+4.692x3+3.785x4+-3.853x5) 4.433))) (=> (and (<= (3.18x1+-2.269x2+-4.53x3+-4.967x4+-4.368x5) 1.352) (<= (4.837x1+-3.914x2+4.692x3+3.785x4+-3.853x5) 4.433)) (<= (4.412x1+2.374x2+3.088x3+-2.112x4+-3.022x5) -4.806))))))"
        assert TQSolver(*FormulaParser.import_tq(formula_our)).solve()
