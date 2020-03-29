import pytest
from uf_solver.uf_solver import UFSolver
from formula_parser.formula_parser import FormulaParser
from copy import deepcopy
import z3
import random
import time


class TestUFSolver:

    @staticmethod
    def test_congruence_closure():
        formula = ('(declare-fun f (Bool Bool) Bool) ' +
                   '(assert (= f(a, b) a)) ' +
                   '(assert (not (= f(f(a, b), b) a)))')
        solver = UFSolver(*FormulaParser.import_uf(formula))
        solver.create_new_decision_level()
        solver._solver._assignment = {1: {"value": True}, 3: {"value": False}}
        conflict_clause, assignments = solver.congruence_closure()
        assert conflict_clause == frozenset({3, -1})

        formula = ('(declare-fun f (Bool) Bool) ' +
                   '(assert (= f(f(f(a))) a)) ' +
                   '(assert (= f(f(f(f(f(a))))) a)) ' +
                   '(assert (not (= f(a) a)))')
        solver = UFSolver(*FormulaParser.import_uf(formula))
        solver.create_new_decision_level()
        solver._solver._assignment = {1: {"value": True}, 2: {"value": True}, 4: {"value": False}}
        conflict_clause, assignments = solver.congruence_closure()
        assert conflict_clause == frozenset({4, -1, -2})

        formula = ('(declare-fun f (Bool) Bool) ' +
                   '(assert (= f(x) f(y))) ' +
                   '(assert (not (= x y)))')
        solver = UFSolver(*FormulaParser.import_uf(formula))
        solver.create_new_decision_level()
        solver._solver._assignment = {1: {"value": True}, 3: {"value": False}}
        conflict_clause, assignments = solver.congruence_closure()
        assert conflict_clause is None

        formula = ('(declare-fun f (Bool) Bool) ' +
                   '(declare-fun g (Bool) Bool) ' +
                   '(assert (= f(g(x)) g(f(x)))) ' +
                   '(assert (= f(g(f(y))) x)) ' +
                   '(assert (= f(y) x)) ' +
                   '(assert (not (= g(f(x)) x)))')
        solver = UFSolver(*FormulaParser.import_uf(formula))
        graph = deepcopy(solver._basic_congruence_graph)
        solver.create_new_decision_level()
        solver._solver._assignment = {1: {"value": True}, 2: {"value": True}, 3: {"value": True}, 5: {"value": False}}
        conflict_clause, assignments = solver.congruence_closure()
        assert conflict_clause == frozenset({5, -1, -2, -3})
        assert solver._basic_congruence_graph._graph == graph._graph    # Make sure the original graph did not change

        # Verify that creating a new decision level copies the last graph
        solver.create_new_decision_level()
        conflict_clause, assignments = solver.congruence_closure()
        assert conflict_clause == frozenset({5, -1, -2, -3})

        # Verify that performing congruence closure again using the same data structure still works
        conflict_clause, assignments = solver.congruence_closure()
        assert conflict_clause == frozenset({5, -1, -2, -3})

        formula = ('(declare-fun f (Bool) Bool) ' +
                   '(assert (= a b)) ' +
                   '(assert (or (or (not (= a b)) (not (= s t))) (= b c))) ' +
                   '(assert (or (or (= s t) (not (= t r))) (= f(s) f(t)))) ' +
                   '(assert (or (or (not (= b c)) (not (= t r))) (= f(s) f(a))))' +
                   '(assert (or (not (= f(s) f(a))) (not (= f(a) f(c)))))')
        solver = UFSolver(*FormulaParser.import_uf(formula))
        solver.create_new_decision_level()
        solver._solver._assignment = {
            1: {"value": True},     # ('=', 'a', 'b')
            7: {"value": True},     # ('=', 's', 't')
            4: {"value": True},     # ('=', 'b', 'c')
            12: {"value": True},   # ('=', 't', 'r')
            # 10: {"value": },      # ('=', ('f', 's'), ('f', 't'))
            15: {"value": True},    # ('=', ('f', 's'), ('f', 'a'))
            20: {"value": False},   # ('=', ('f', 'a'), ('f', 'c'))
        }
        conflict_clause, assignments = solver.congruence_closure()
        # assert solver.congruence_closure() == frozenset({20, -1, -4})  # <- this is the minimal
        assert conflict_clause == frozenset({-15, -12, 20, -7, -4, -1})

        solver = UFSolver(*FormulaParser.import_uf(formula))
        solver.create_new_decision_level()
        solver._solver._assignment = {
            1: {"value": True},  # ('=', 'a', 'b')
            7: {"value": True},  # ('=', 's', 't')
            4: {"value": True},  # ('=', 'b', 'c')
            12: {"value": False},  # ('=', 't', 'r')
            # 10: {"value": },      # ('=', ('f', 's'), ('f', 't'))
            15: {"value": True},  # ('=', ('f', 's'), ('f', 'a'))
            20: {"value": False},  # ('=', ('f', 'a'), ('f', 'c'))
        }
        conflict_clause, assignments = solver.congruence_closure()
        assert conflict_clause == frozenset({-15, 20, -7, -4, -1})

        solver = UFSolver(*FormulaParser.import_uf(formula))
        solver.create_new_decision_level()
        solver._solver._assignment = {
            1: {"value": True},  # ('=', 'a', 'b')
            7: {"value": True},  # ('=', 's', 't')
            4: {"value": True},  # ('=', 'b', 'c')
            12: {"value": False},  # ('=', 't', 'r')
            10: {"value": True},  # ('=', ('f', 's'), ('f', 't'))
            15: {"value": False},  # ('=', ('f', 's'), ('f', 'a'))
            20: {"value": True},  # ('=', ('f', 'a'), ('f', 'c'))
        }
        conflict_clause, assignments = solver.congruence_closure()
        assert conflict_clause is None

    @staticmethod
    def test_theory_propagation():
        formula = ('(declare-fun f (Bool) Bool) ' +
                   '(assert (= a b)) ' +
                   '(assert (or (or (not (= a b)) (not (= s t))) (= b c))) ' +
                   '(assert (or (or (= s t) (not (= t r))) (= f(s) f(t)))) ' +
                   '(assert (or (or (not (= b c)) (not (= t r))) (= f(s) f(a))))' +
                   '(assert (or (not (= f(s) f(a))) (not (= f(a) f(c)))))')
        solver = UFSolver(*FormulaParser.import_uf(formula))
        solver._solver._create_new_decision_level()
        solver._solver._assignment = {
            1: {"value": True},  # ('=', 'a', 'b')
            7: {"value": True},  # ('=', 's', 't')
        }
        conflict_clause, assignments = solver.congruence_closure()
        assert conflict_clause is None
        assert assignments == [10]

        solver._solver._assignment = {
            1: {"value": True},  # ('=', 'a', 'b')
            7: {"value": True},  # ('=', 's', 't')
            10: {"value": True},  # ('=', ('f', 's'), ('f', 't'))
            4: {"value": True},  # ('=', 'b', 'c')
        }
        conflict_clause, assignments = solver.congruence_closure()
        assert conflict_clause is None
        assert assignments == [20]

    @staticmethod
    def test_integration():
        formula = ('(declare-fun f (Bool) Bool) ' +
                   '(assert (= a b)) ' +
                   '(assert (or (or (not (= a b)) (not (= s t))) (= b c))) ' +
                   '(assert (or (or (= s t) (not (= t r))) (= f(s) f(t)))) ' +
                   '(assert (or (or (not (= b c)) (not (= t r))) (= f(s) f(a))))' +
                   '(assert (or (not (= f(s) f(a))) (not (= f(a) f(c)))))')
        solver = UFSolver(*FormulaParser.import_uf(formula))
        assert solver.solve()

        formula = ('(declare-fun f (Bool Bool) Bool) ' +
                   '(assert (= f(a, b) a)) ' +
                   '(assert (not (= f(f(a, b), b) a)))')
        solver = UFSolver(*FormulaParser.import_uf(formula))
        assert not solver.solve()

        formula = ('(declare-fun f (Bool) Bool) ' +
                   '(assert (= f(f(f(a))) a)) ' +
                   '(assert (= f(f(f(f(f(a))))) a)) ' +
                   '(assert (not (= f(a) a)))')
        solver = UFSolver(*FormulaParser.import_uf(formula))
        assert not solver.solve()

        formula = ('(declare-fun f (Bool) Bool) ' +
                   '(assert (= f(x) f(y))) ' +
                   '(assert (not (= x y)))')
        solver = UFSolver(*FormulaParser.import_uf(formula))
        assert solver.solve()

        formula = ('(declare-fun f (Bool) Bool) ' +
                   '(declare-fun g (Bool) Bool) ' +
                   '(assert (= f(g(x)) g(f(x)))) ' +
                   '(assert (= f(g(f(y))) x)) ' +
                   '(assert (= f(y) x)) ' +
                   '(assert (not (= g(f(x)) x)))')
        solver = UFSolver(*FormulaParser.import_uf(formula))
        assert not solver.solve()

    @staticmethod
    def test_boolean_formulas():
        formula = "(declare-fun f (Bool) Bool) (declare-fun g (Bool Bool) Bool) (assert (and (not 1) (1)))"
        assert not UFSolver(*FormulaParser.import_uf(formula)).solve()

        formula = "(declare-fun f (Bool) Bool) (declare-fun g (Bool Bool) Bool) (assert (or (1) (not 2)))"
        assert UFSolver(*FormulaParser.import_uf(formula)).solve()

        formula = "(declare-fun f (Bool) Bool) (declare-fun g (Bool Bool) Bool) (assert (or (not (not 4)) (not 4)))"
        assert UFSolver(*FormulaParser.import_uf(formula)).solve()

    @staticmethod
    @pytest.mark.parametrize("variable_num, operator_num", [(5, clause_num) for clause_num in list(range(1, 500))])
    def test_random_boolean_formula(variable_num: int, operator_num: int):
        # Generates a random formula and compares our solver to Z3

        # Generate formula
        all_vars = list(range(1, variable_num + 1))
        subformulas_z3 = [z3.Bool(str(cur_literal)) for cur_literal in all_vars]
        subformulas_z3.extend([z3.Not(cur_literal) for cur_literal in subformulas_z3])
        subformulas_our = [str(cur_literal) for cur_literal in all_vars]
        subformulas_our.extend([("not " + cur_literal) for cur_literal in subformulas_our])

        for cur_operator_idx in range(operator_num):
            param1_idx = random.randint(1, len(subformulas_z3)) - 1
            param1_z3 = subformulas_z3[param1_idx]
            param1_our = subformulas_our[param1_idx]

            random_operator = random.randint(1, 5)
            if random_operator == 1:
                cur_subformula_z3 = z3.Not(param1_z3)
                cur_subformula_our = "not (" + param1_our + ")"
            else:   # Binary operators
                param2_idx = random.randint(1, len(subformulas_z3)) - 1
                param2_z3 = subformulas_z3[param2_idx]
                param2_our = subformulas_our[param2_idx]
                if random_operator == 2:
                    cur_subformula_z3 = z3.And(param1_z3, param2_z3)
                    cur_subformula_our = "and (" + param1_our + ") (" + param2_our + ")"
                elif random_operator == 3:
                    cur_subformula_z3 = z3.Or(param1_z3, param2_z3)
                    cur_subformula_our = "or (" + param1_our + ") (" + param2_our + ")"
                elif random_operator == 4:
                    cur_subformula_z3 = z3.Implies(param1_z3, param2_z3)
                    cur_subformula_our = "=> (" + param1_our + ") (" + param2_our + ")"
                elif random_operator == 5:
                    cur_subformula_z3 = (param1_z3 == param2_z3)
                    cur_subformula_our = "<=> (" + param1_our + ") (" + param2_our + ")"
            subformulas_z3.append(cur_subformula_z3)
            subformulas_our.append(cur_subformula_our)

        # Solve with Z3
        z3_solver = z3.Solver()
        z3_solver.add(subformulas_z3[-1])
        start_time_z3 = time.time()
        is_sat_z3 = (z3_solver.check() == z3.sat)
        end_time_z3 = time.time()

        # Solve with ours
        formula_our = "(assert (" + subformulas_our[-1] + "))"
        our_solver = UFSolver(*FormulaParser.import_uf(formula_our))
        start_time_our = time.time()
        is_sat_our = our_solver.solve()
        end_time_our = time.time()

        print("Z3:\t\t", end_time_z3 - start_time_z3)
        print("Our:\t", end_time_our - start_time_our)
        assert is_sat_our is is_sat_z3

    @staticmethod
    @pytest.mark.parametrize("variable_num, operator_num", [(5, clause_num) for clause_num in list(range(1, 100)) * 10])
    def test_random_uf_formula(variable_num: int, operator_num: int):
        # Generate formula
        all_variables = list(range(1, variable_num + 1))
        z3_f = z3.Function('f', z3.IntSort(), z3.IntSort())
        subformulas_z3 = [z3.Int(str(cur_literal)) for cur_literal in all_variables]
        equations_z3 = []
        subformulas_our = [str(cur_literal) for cur_literal in all_variables]
        equations_our = []

        for cur_operator_idx in range(operator_num):
            first_parameter_idx = random.randint(1, len(subformulas_z3)) - 1
            first_parameter_z3 = subformulas_z3[first_parameter_idx]
            first_parameter_our = subformulas_our[first_parameter_idx]

            random_operator = random.randint(1, 3)
            if random_operator == 1:
                cur_subformula_z3 = z3_f(first_parameter_z3)
                cur_subformula_our = "f(" + first_parameter_our + ")"
                subformulas_z3.append(cur_subformula_z3)
                subformulas_our.append(cur_subformula_our)
            else:
                param2_idx = random.randint(1, len(subformulas_z3)) - 1
                param2_z3 = subformulas_z3[param2_idx]
                param2_our = subformulas_our[param2_idx]
                if random_operator == 2:
                    cur_subformula_z3 = (first_parameter_z3 == param2_z3)
                    cur_subformula_our = "(assert (= (" + first_parameter_our + ") (" + param2_our + "))"
                elif random_operator == 3:
                    cur_subformula_z3 = (first_parameter_z3 != param2_z3)
                    cur_subformula_our = "(assert (not (= (" + first_parameter_our + ") (" + param2_our + \
                                         ")))"
                equations_z3.append(cur_subformula_z3)
                equations_our.append(cur_subformula_our)

        # Solve with Z3
        formula_z3 = z3.And(equations_z3)
        z3_solver = z3.Solver()
        z3_solver.add(formula_z3)
        start_time_z3 = time.time()
        is_sat_z3 = (z3_solver.check() == z3.sat)
        end_time_z3 = time.time()

        # Solve with ours
        formula_our = "(declare-fun f (Int) Int) " + ' '.join(equations_our)
        our_solver = UFSolver(*FormulaParser.import_uf(formula_our))
        start_time_our = time.time()
        is_sat_our = our_solver.solve()
        end_time_our = time.time()

        print("Z3:\t\t", end_time_z3 - start_time_z3)
        print("Our:\t", end_time_our - start_time_our)
        assert is_sat_our is is_sat_z3
