import pytest
from smt_solver.sat_solver.tests.test_sat_solver import TestSATSolver
from smt_solver.uf_solver.tests.test_uf_solver import TestUFSolver
from smt_solver.tq_solver.tests.test_tq_solver import TestTQSolver
from smt_solver.smt_solver import SMTSolver
from random import randint
import numpy as np


class TestSMTSolver:
    @staticmethod
    @pytest.mark.parametrize("variable_num, equation_num, function_num, coefficient_limits, operator_num",
                             # [(5, 10, 2, (-5, 5), operator_num) for operator_num in np.full(100000, 10)]
                             np.full((1000, 5), (5, 10, 2, (-5, 5), 10))
                             )
    def test_random_formula(variable_num: int, equation_num: int, function_num: int, coefficient_limits: (int, int),
                            operator_num: int):
        formula_z3, formula_our, formula_type = None, None, randint(1, 3)
        if formula_type == 1:
            formula_z3, formula_our = TestUFSolver.generate_random_boolean_formula(variable_num, operator_num)
        elif formula_type == 2:
            formula_z3, formula_our = TestUFSolver.generate_random_uf_formula(variable_num, equation_num, function_num,
                                                                              operator_num)
        elif formula_type == 3:
            formula_z3, formula_our = TestTQSolver.generate_random_tq_formula(variable_num, equation_num,
                                                                              coefficient_limits, operator_num)
        if (formula_z3 is None) or (formula_our is None):
            return
        print("\n\n", "Z3 formula: ", formula_z3, "\n", "Our formula: ", formula_our)
        assert TestSATSolver.compare_to_z3(formula_z3, SMTSolver(formula_our))
