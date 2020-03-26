import pytest
from smt_solver.smt_solver import SMTSolver
from formula_parser.formula_parser import FormulaParser
from copy import deepcopy
import z3
import random
import time


class TestSMTSolver:

    @staticmethod
    def test_congruence_closure():
        formula = ('(declare-fun f (Bool Bool) Bool) ' +
                   '(assert (= f(a, b) a)) ' +
                   '(assert (not (= f(f(a, b), b) a)))')
        solver = SMTSolver(*FormulaParser.import_uf(formula))
        solver.create_new_decision_level()
        solver._solver._assignment = {1: {"value": True}, 3: {"value": False}}
        conflict_clause, assignments = solver.congruence_closure()
        assert conflict_clause == frozenset({3, -1})

        formula = ('(declare-fun f (Bool) Bool) ' +
                   '(assert (= f(f(f(a))) a)) ' +
                   '(assert (= f(f(f(f(f(a))))) a)) ' +
                   '(assert (not (= f(a) a)))')
        solver = SMTSolver(*FormulaParser.import_uf(formula))
        solver.create_new_decision_level()
        solver._solver._assignment = {1: {"value": True}, 2: {"value": True}, 4: {"value": False}}
        conflict_clause, assignments = solver.congruence_closure()
        assert conflict_clause == frozenset({4, -1, -2})

        formula = ('(declare-fun f (Bool) Bool) ' +
                   '(assert (= f(x) f(y))) ' +
                   '(assert (not (= x y)))')
        solver = SMTSolver(*FormulaParser.import_uf(formula))
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
        solver = SMTSolver(*FormulaParser.import_uf(formula))
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
        solver = SMTSolver(*FormulaParser.import_uf(formula))
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

        solver = SMTSolver(*FormulaParser.import_uf(formula))
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

        solver = SMTSolver(*FormulaParser.import_uf(formula))
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
        solver = SMTSolver(*FormulaParser.import_uf(formula))
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
        solver = SMTSolver(*FormulaParser.import_uf(formula))
        assert solver.solve()

        formula = ('(declare-fun f (Bool Bool) Bool) ' +
                   '(assert (= f(a, b) a)) ' +
                   '(assert (not (= f(f(a, b), b) a)))')
        solver = SMTSolver(*FormulaParser.import_uf(formula))
        assert not solver.solve()

        formula = ('(declare-fun f (Bool) Bool) ' +
                   '(assert (= f(f(f(a))) a)) ' +
                   '(assert (= f(f(f(f(f(a))))) a)) ' +
                   '(assert (not (= f(a) a)))')
        solver = SMTSolver(*FormulaParser.import_uf(formula))
        assert not solver.solve()

        formula = ('(declare-fun f (Bool) Bool) ' +
                   '(assert (= f(x) f(y))) ' +
                   '(assert (not (= x y)))')
        solver = SMTSolver(*FormulaParser.import_uf(formula))
        assert solver.solve()

        formula = ('(declare-fun f (Bool) Bool) ' +
                   '(declare-fun g (Bool) Bool) ' +
                   '(assert (= f(g(x)) g(f(x)))) ' +
                   '(assert (= f(g(f(y))) x)) ' +
                   '(assert (= f(y) x)) ' +
                   '(assert (not (= g(f(x)) x)))')
        solver = SMTSolver(*FormulaParser.import_uf(formula))
        assert not solver.solve()

    @staticmethod
    def test_boolean_formulas():
        formula1 = "(declare-fun f (Bool) Bool) (declare-fun g (Bool Bool) Bool) (assert (and (not 1) (1)))"
        assert not SMTSolver(*FormulaParser.import_uf(formula1)).solve()

        formula2 = "(declare-fun f (Bool) Bool) (declare-fun g (Bool Bool) Bool) (assert (or (1) (not 2)))"
        assert SMTSolver(*FormulaParser.import_uf(formula2)).solve()

        formula3 = "(declare-fun f (Bool) Bool) (declare-fun g (Bool Bool) Bool) (assert (or (not (not 4)) (not 4)))"
        assert SMTSolver(*FormulaParser.import_uf(formula3)).solve()

    @staticmethod
    @pytest.mark.parametrize("variable_num, operator_num", [(5, clause_num) for clause_num in list(range(1, 100))])
    def test_random_formula(variable_num: int, operator_num: int):
        # Generates a random formula and compares our solver to Z3
        f = z3.Function('f', z3.BoolSort(), z3.BoolSort())
        g = z3.Function('g', z3.BoolSort(), z3.BoolSort(), z3.BoolSort())
        h = z3.Function('h', z3.BoolSort(), z3.BoolSort(), z3.BoolSort(), z3.BoolSort())

        # Generate formula
        all_variables = list(range(1, variable_num + 1))
        all_subformulas_z3 = [z3.Bool(str(cur_literal)) for cur_literal in all_variables]
        all_subformulas_z3.extend([z3.Not(cur_literal) for cur_literal in all_subformulas_z3])
        all_uf_subformulas_z3 = [z3.Bool(str(cur_literal)) for cur_literal in all_variables]
        all_uf_equations_z3 = []
        all_subformulas_our = [str(cur_literal) for cur_literal in all_variables]
        all_subformulas_our.extend([("not " + cur_literal) for cur_literal in all_subformulas_our])
        all_uf_subformulas_our = [str(cur_literal) for cur_literal in all_variables]
        all_uf_equations_our = []

        for cur_operator_idx in range(operator_num):
            cur_subformula_z3 = None
            cur_subformula_our = None
            random_operator = random.randint(1, 10)

            first_parameter_idx = random.randint(1, len(all_subformulas_z3)) - 1
            first_parameter_z3 = all_subformulas_z3[first_parameter_idx]
            first_parameter_our = all_subformulas_our[first_parameter_idx]
            if random_operator == 1:
                cur_subformula_z3 = z3.Not(first_parameter_z3)
                cur_subformula_our = "not (" + first_parameter_our + ")"
            elif random_operator <= 5:
                # Binary operators
                second_parameter_idx = random.randint(1, len(all_subformulas_z3)) - 1
                second_parameter_z3 = all_subformulas_z3[second_parameter_idx]
                second_parameter_our = all_subformulas_our[second_parameter_idx]
                if random_operator == 2:
                    cur_subformula_z3 = z3.And(first_parameter_z3, second_parameter_z3)
                    cur_subformula_our = "and (" + first_parameter_our + ") (" + second_parameter_our + ")"
                elif random_operator == 3:
                    cur_subformula_z3 = z3.Or(first_parameter_z3, second_parameter_z3)
                    cur_subformula_our = "or (" + first_parameter_our + ") (" + second_parameter_our + ")"
                elif random_operator == 4:
                    cur_subformula_z3 = z3.Implies(first_parameter_z3, second_parameter_z3)
                    cur_subformula_our = "=> (" + first_parameter_our + ") (" + second_parameter_our + ")"
                elif random_operator == 5:
                    cur_subformula_z3 = (first_parameter_z3 == second_parameter_z3)
                    cur_subformula_our = "<=> (" + first_parameter_our + ") (" + second_parameter_our + ")"
            else:
                first_parameter_idx = random.randint(1, len(all_uf_subformulas_z3)) - 1
                first_parameter_z3 = all_uf_subformulas_z3[first_parameter_idx]
                first_parameter_our = all_uf_subformulas_our[first_parameter_idx]
                if random_operator == 6:
                    cur_subformula_z3 = f(first_parameter_z3)
                    cur_subformula_our = "f(" + first_parameter_our + ")"
                    all_uf_subformulas_z3.append(cur_subformula_z3)
                    all_uf_subformulas_our.append(cur_subformula_our)
                else:
                    second_parameter_idx = random.randint(1, len(all_uf_subformulas_z3)) - 1
                    second_parameter_z3 = all_uf_subformulas_z3[second_parameter_idx]
                    second_parameter_our = all_uf_subformulas_our[second_parameter_idx]
                    if random_operator == 7:
                        cur_subformula_z3 = g(first_parameter_z3, second_parameter_z3)
                        cur_subformula_our = "g(" + first_parameter_our + "," + second_parameter_our + ")"
                        all_uf_subformulas_z3.append(cur_subformula_z3)
                        all_uf_subformulas_our.append(cur_subformula_our)
                    elif random_operator == 8:
                        third_parameter_idx = random.randint(1, len(all_uf_subformulas_z3)) - 1
                        third_parameter_z3 = all_uf_subformulas_z3[third_parameter_idx]
                        third_parameter_our = all_uf_subformulas_our[third_parameter_idx]
                        cur_subformula_z3 = h(first_parameter_z3, second_parameter_z3, third_parameter_z3)
                        cur_subformula_our = "h(" + first_parameter_our + "," + second_parameter_our + "," + \
                                             third_parameter_our + ")"
                        all_uf_subformulas_z3.append(cur_subformula_z3)
                        all_uf_subformulas_our.append(cur_subformula_our)
                    elif random_operator == 9:
                        cur_subformula_z3 = (first_parameter_z3 == second_parameter_z3)
                        cur_subformula_our = "(assert (= (" + first_parameter_our + ") (" + second_parameter_our + "))"
                        all_uf_equations_z3.append(cur_subformula_z3)
                        all_uf_equations_our.append(cur_subformula_our)
                    elif random_operator == 10:
                        cur_subformula_z3 = (first_parameter_z3 != second_parameter_z3)
                        cur_subformula_our = "(assert (not (= (" + first_parameter_our + ") (" + \
                                             second_parameter_our + ")))"
                        all_uf_equations_z3.append(cur_subformula_z3)
                        all_uf_equations_our.append(cur_subformula_our)
                continue
            all_subformulas_z3.append(cur_subformula_z3)
            all_subformulas_our.append(cur_subformula_our)

        formula_z3 = z3.And(*all_uf_equations_z3)
        formula_our_text = "(declare-fun f (Bool) Bool) (declare-fun g (Bool Bool) Bool) " + \
                           ' '.join(all_uf_equations_our)
        print(formula_our_text)

        # Solve with Z3
        z3_solver = z3.Solver()
        z3_solver.add(formula_z3)
        start_time_z3 = time.time()
        is_sat_z3 = (z3_solver.check() == z3.sat)
        end_time_z3 = time.time()

        # Solve with ours
        start_time_our = time.time()
        our_solver = SMTSolver(*FormulaParser.import_uf(formula_our_text))
        is_sat_our = our_solver.solve()
        end_time_our = time.time()

        print()
        print("Is sat? ", is_sat_z3)
        print("Z3:\t\t", end_time_z3 - start_time_z3)
        print("Our:\t", end_time_our - start_time_our)
        print("Z3 formula: ", formula_z3)
        print("Our formula: ", formula_our_text)
        assert is_sat_our is is_sat_z3

    @staticmethod
    @pytest.mark.parametrize("variable_num, operator_num", [(5, clause_num) for clause_num in list(range(1, 100)) * 10])
    def test_random_formula_hard(variable_num: int, operator_num: int):
        # Generates a random formula and compares our solver to Z3
        f = z3.Function('f', z3.BoolSort(), z3.BoolSort())

        # Generate formula
        all_variables = list(range(1, variable_num + 1))
        all_variables_z3 = [z3.Bool(str(cur_literal)) for cur_literal in all_variables]
        all_uf_subformulas_z3 = [z3.Bool(str(cur_literal)) for cur_literal in all_variables]
        all_uf_equations_z3 = []
        all_variables_our = [str(cur_literal) for cur_literal in all_variables]
        all_uf_subformulas_our = [str(cur_literal) for cur_literal in all_variables]
        all_uf_equations_our = []

        for cur_operator_idx in range(operator_num):
            random_operator = random.randint(1, 3)

            if random_operator == 1:
                first_parameter_idx = random.randint(1, len(all_variables_z3)) - 1
                first_parameter_z3 = all_variables_z3[first_parameter_idx]
                first_parameter_our = all_variables_our[first_parameter_idx]
                cur_subformula_z3 = f(first_parameter_z3)
                cur_subformula_our = "f(" + first_parameter_our + ")"
                all_uf_subformulas_z3.append(cur_subformula_z3)
                all_uf_subformulas_our.append(cur_subformula_our)
            elif random_operator == 2:
                first_parameter_idx = random.randint(1, len(all_uf_subformulas_z3)) - 1
                first_parameter_z3 = all_uf_subformulas_z3[first_parameter_idx]
                first_parameter_our = all_uf_subformulas_our[first_parameter_idx]
                second_parameter_idx = random.randint(1, len(all_uf_subformulas_z3)) - 1
                second_parameter_z3 = all_uf_subformulas_z3[second_parameter_idx]
                second_parameter_our = all_uf_subformulas_our[second_parameter_idx]

                cur_subformula_z3 = (first_parameter_z3 == second_parameter_z3)
                cur_subformula_our = "(assert (= (" + first_parameter_our + ") (" + second_parameter_our + "))"
                all_uf_equations_z3.append(cur_subformula_z3)
                all_uf_equations_our.append(cur_subformula_our)
            elif random_operator == 3:
                first_parameter_idx = random.randint(1, len(all_uf_subformulas_z3)) - 1
                first_parameter_z3 = all_uf_subformulas_z3[first_parameter_idx]
                first_parameter_our = all_uf_subformulas_our[first_parameter_idx]
                second_parameter_idx = random.randint(1, len(all_uf_subformulas_z3)) - 1
                second_parameter_z3 = all_uf_subformulas_z3[second_parameter_idx]
                second_parameter_our = all_uf_subformulas_our[second_parameter_idx]

                cur_subformula_z3 = (first_parameter_z3 != second_parameter_z3)
                cur_subformula_our = "(assert (not (= (" + first_parameter_our + ") (" + second_parameter_our + ")))"
                all_uf_equations_z3.append(cur_subformula_z3)
                all_uf_equations_our.append(cur_subformula_our)

        formula_z3 = z3.And(*all_uf_equations_z3)
        formula_our_text = "(declare-fun f (Bool) Bool) (declare-fun g (Bool Bool) Bool) " + \
                           ' '.join(all_uf_equations_our)
        print(formula_our_text)

        # Solve with Z3
        z3_solver = z3.Solver()
        z3_solver.add(formula_z3)
        start_time_z3 = time.time()
        is_sat_z3 = (z3_solver.check() == z3.sat)
        end_time_z3 = time.time()

        # Solve with ours
        start_time_our = time.time()
        our_solver = SMTSolver(*FormulaParser.import_uf(formula_our_text))
        is_sat_our = our_solver.solve()
        end_time_our = time.time()

        print()
        print("Is sat? ", is_sat_z3)
        print("Z3:\t\t", end_time_z3 - start_time_z3)
        print("Our:\t", end_time_our - start_time_our)
        print("Z3 formula: ", formula_z3)
        print("Our formula: ", formula_our_text)
        assert is_sat_our is is_sat_z3
