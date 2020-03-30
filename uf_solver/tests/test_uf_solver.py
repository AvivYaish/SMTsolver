import pytest
from uf_solver.uf_solver import UFSolver
from formula_parser.formula_parser import FormulaParser
from sat_solver.tests.test_sat_solver import TestSATSolver
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
        formula_z3, formula_our_txt, formula_our_parsed = TestSATSolver.generate_random_formula(variable_num,
                                                                                                operator_num)
        formula_our = "(assert (" + formula_our_txt + "))"
        assert TestSATSolver.compare_to_z3(formula_z3, UFSolver(*FormulaParser.import_uf(formula_our)))

    @staticmethod
    def generate_random_equations(variable_num: int, operator_num: int):
        all_variables = list(range(1, variable_num + 1))
        z3_f = z3.Function('f', z3.IntSort(), z3.IntSort())
        subformulas_z3, equations_z3 = [z3.Int(str(cur_literal)) for cur_literal in all_variables], []
        subformulas_our_txt, equations_our_txt = [str(cur_literal) for cur_literal in all_variables], []
        subformulas_our, equations_our = [str(cur_literal) for cur_literal in all_variables], []

        for cur_operator_idx in range(operator_num):
            param1_idx = random.randint(1, len(subformulas_z3)) - 1
            param1_z3, param1_our_txt, param1_our = \
                subformulas_z3[param1_idx], subformulas_our_txt[param1_idx], subformulas_our[param1_idx]
            random_operator = random.randint(1, 3)
            if random_operator == 1:
                cur_subformula_z3, cur_subformula_our_txt, cur_subformula_our = \
                    z3_f(param1_z3), "f(" + param1_our_txt + ")", ("f", param1_our)
                subformulas_z3.append(cur_subformula_z3)
                subformulas_our_txt.append(cur_subformula_our_txt)
                subformulas_our.append(cur_subformula_our)
            else:
                param2_idx = random.randint(1, len(subformulas_z3)) - 1
                param2_z3, param2_our_txt, param2_our = \
                    subformulas_z3[param2_idx], subformulas_our_txt[param2_idx], subformulas_our[param2_idx]
                if random_operator == 2:
                    cur_subformula_z3, cur_subformula_our_txt, cur_subformula_our = \
                        (param1_z3 == param2_z3), "(= (" + param1_our_txt + ") (" + param2_our_txt + ")", \
                        ("=", param1_our, param2_our)
                elif random_operator == 3:
                    cur_subformula_z3, cur_subformula_our_txt, cur_subformula_our = \
                        (param1_z3 != param2_z3), "(not (= (" + param1_our_txt + ") (" + param2_our_txt + "))", \
                        ("not", ("=", param1_our, param2_our))
                equations_z3.append(cur_subformula_z3)
                equations_our_txt.append(cur_subformula_our_txt)
                equations_our.append(cur_subformula_our)
        return equations_z3, equations_our_txt, equations_our

    @staticmethod
    @pytest.mark.parametrize("variable_num, operator_num", [(5, clause_num) for clause_num in list(range(1, 100)) * 10])
    def test_random_uf_formula(variable_num: int, operator_num: int):
        equations_z3, equations_our_txt, equations_our = \
            TestUFSolver.generate_random_equations(variable_num, operator_num)
        formula_z3, formula_our_txt, formula_our = \
            TestSATSolver.generate_random_formula(0, operator_num, equations_z3, equations_our_txt, equations_our)
        formula_our_txt = "(declare-fun f (Int) Int) (assert (" + formula_our_txt + "))"
        print("Z3 formula: ", formula_z3)
        print("Our formula: ", formula_our_txt)
        assert TestSATSolver.compare_to_z3(formula_z3, UFSolver(*FormulaParser.import_uf(formula_our_txt)))
