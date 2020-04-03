import pytest
from uf_solver.uf_solver import UFSolver
from formula_parser.formula_parser import FormulaParser
from sat_solver.tests.test_sat_solver import TestSATSolver
from copy import deepcopy
import z3
import random


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
        assert solver._basic_congruence_graph._graph == graph._graph  # Make sure the original graph did not change

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
            1: {"value": True},  # ('=', 'a', 'b')
            7: {"value": True},  # ('=', 's', 't')
            4: {"value": True},  # ('=', 'b', 'c')
            12: {"value": True},  # ('=', 't', 'r')
            # 10: {"value": },      # ('=', ('f', 's'), ('f', 't'))
            15: {"value": True},  # ('=', ('f', 's'), ('f', 'a'))
            20: {"value": False},  # ('=', ('f', 'a'), ('f', 'c'))
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
    @pytest.mark.parametrize("variable_num, operator_num", [(5, clause_num) for clause_num in list(range(1, 50))])
    def test_random_boolean_formula(variable_num: int, operator_num: int):
        formula_z3, formula_our_txt, formula_our_parsed = TestSATSolver.generate_random_formula(variable_num,
                                                                                                operator_num)
        formula_our = "(assert (" + formula_our_txt + "))"
        assert TestSATSolver.compare_to_z3(formula_z3, UFSolver(*FormulaParser.import_uf(formula_our)))

    @staticmethod
    def generate_random_equations(variable_num: int, operator_num: int, function_num):
        all_variables = list(range(1, variable_num + 1))
        subformulas_z3, equations_z3 = [z3.Int("x" + str(cur_literal)) for cur_literal in all_variables], []
        subformulas_our_txt, equations_our_txt = ["x" + str(cur_literal) for cur_literal in all_variables], []
        subformulas_our, equations_our = ["x" + str(cur_literal) for cur_literal in all_variables], []
        f, g = z3.Function('f', z3.IntSort(), z3.IntSort()), z3.Function('g', z3.IntSort(), z3.IntSort())

        for cur_operator_idx in range(operator_num):
            param1_idx = random.randint(1, len(subformulas_z3)) - 1
            param1_z3, param1_our_txt, param1_our = \
                subformulas_z3[param1_idx], subformulas_our_txt[param1_idx], subformulas_our[param1_idx]
            random_operator = random.randint(1, 4)
            if random_operator <= 2:
                if (random_operator == 1) or (function_num <= 1):
                    cur_subformula_z3, cur_subformula_our_txt, cur_subformula_our = \
                        f(param1_z3), "f(" + param1_our_txt + ")", ("f", param1_our)
                elif random_operator == 2:
                    cur_subformula_z3, cur_subformula_our_txt, cur_subformula_our = \
                        g(param1_z3), "g(" + param1_our_txt + ")", ("g", param1_our)
                subformulas_z3.append(cur_subformula_z3)
                subformulas_our_txt.append(cur_subformula_our_txt)
                subformulas_our.append(cur_subformula_our)
            else:
                param2_idx = random.randint(1, len(subformulas_z3)) - 1
                param2_z3, param2_our_txt, param2_our = \
                    subformulas_z3[param2_idx], subformulas_our_txt[param2_idx], subformulas_our[param2_idx]
                if random_operator == 3:
                    cur_subformula_z3, cur_subformula_our_txt, cur_subformula_our = \
                        (param1_z3 == param2_z3), "= (" + param1_our_txt + ") (" + param2_our_txt + ")", \
                        ("=", param1_our, param2_our)
                elif random_operator == 4:
                    cur_subformula_z3, cur_subformula_our_txt, cur_subformula_our = \
                        (param1_z3 != param2_z3), "not (= (" + param1_our_txt + ") (" + param2_our_txt + "))", \
                        ("not", ("=", param1_our, param2_our))
                equations_z3.append(cur_subformula_z3)
                equations_our_txt.append(cur_subformula_our_txt)
                equations_our.append(cur_subformula_our)
        return equations_z3, equations_our_txt, equations_our

    @staticmethod
    def test_bad():
        """
        FAILED    [ 26%]Z3 formula:  And(1 == f(f(3)),
    Implies(f(4) != f(f(3)),
            And(Not(f(f(4)) != f(f(f(3)))), f(3) == f(3))))
Our formula:
        """
        # Works just because of the simplification
        formula = "(declare-fun f (Int) Int) (assert (and (= (1) (f(f(3)))) (=> (not (= (f(4)) (f(f(3))))) (and (not (not (= (f(f(4))) (f(f(f(3))))))) (= (f(3)) (f(3)))))))"
        easier_formula = "(declare-fun f (Int) Int) (assert (=> (not (= (f(4)) (f(f(3))))) (and (not (not (= (f(f(4))) (f(f(f(3))))))) (= (f(3)) (f(3))))))"
        assert UFSolver(*FormulaParser.import_uf(easier_formula)).solve()

    @staticmethod
    def test_bad2():
        """
        Z3 formula:  Or(And(f(f(f(5))) == f(f(f(f(f(5))))),
       Or(f(4) == f(5), f(f(f(f(5)))) == f(5))),
   f(f(5)) == f(5))
Our formula:  (declare-fun f (Int) Int) (assert (or (and (= (f(f(f(5)))) (f(f(f(f(f(5))))))) (or (= (f(4)) (f(5))) (= (f(f(f(f(5))))) (f(5))))) (= (f(f(5))) (f(5)))))

Is SAT? True
        """
        formula = "(declare-fun f (Int) Int) (assert (or (and (= (f(f(f(5)))) (f(f(f(f(f(5))))))) (or (= (f(4)) (f(5))) (= (f(f(f(f(5))))) (f(5))))) (= (f(f(5))) (f(5)))))"
        assert UFSolver(*FormulaParser.import_uf(formula)).solve()

    @staticmethod
    def test_bad3():
        """
        FAILED  [ 15%]
Z3 formula:  Implies(Or(f(f(1)) == 2, 3 != f(f(1))),
        And(And(3 == 2, 2 != 3), f(1) != 1))
Our formula:  (declare-fun f (Int) Int) (assert (=> (or (= (f(f(1))) (2)) (not (= (3) (f(f(1)))))) (and (and (= (3) (2)) (not (= (2) (3)))) (not (= (f(1)) (1))))))

Is SAT? False
Z3:		 0.02293848991394043
Our:	 0.0

        """
        formula = "(declare-fun f (Int) Int) (assert (=> (or (= (f(f(1))) (2)) (not (= (3) (f(f(1)))))) (and (and (= (3) (2)) (not (= (2) (3)))) (not (= (f(1)) (1))))))"
        assert UFSolver(*FormulaParser.import_uf(formula)).solve()

    @staticmethod
    def test_bad4():
        """
        FAILED  [ 31%]
Z3 formula:  Implies(Implies(3 == 1, 3 != f(1)),
        And(Not(f(3) != f(1)), Implies(f(3) != 1, 2 == 1)))
Our formula:  (declare-fun f (Int) Int) (assert (=> (=> (= (3) (1)) (not (= (3) (f(1))))) (and (not (not (= (f(3)) (f(1))))) (=> (not (= (f(3)) (1))) (= (2) (1))))))

Is SAT? True
Z3:		 0.007979869842529297
Our:	 0.0
        """
        formula = "(declare-fun f (Int) Int) (assert (=> (=> (= (3) (1)) (not (= (3) (f(1))))) (and (not (not (= (f(3)) (f(1))))) (=> (not (= (f(3)) (1))) (= (2) (1))))))"
        assert UFSolver(*FormulaParser.import_uf(formula)).solve()

    @staticmethod
    def test_bad5():
        """
        FAILED  [ 55%]
Z3 formula:  Or(And(And(3 == 1, Not(1 == 2)), 3 == 1),
   And(3 == 2, 2 != 1))
Our formula:  (declare-fun f (Int) Int) (assert (or (and (and (= (3) (1)) (not (= (1) (2)))) (= (3) (1))) (and (= (3) (2)) (not (= (2) (1))))))

Is SAT? False
Z3:		 0.019948720932006836
Our:	 0.0
"""
        formula = "(declare-fun f (Int) Int) (assert (or (and (and (= (3) (1)) (not (= (1) (2)))) (= (3) (1))) (and (= (3) (2)) (not (= (2) (1))))))"
        assert UFSolver(*FormulaParser.import_uf(formula)).solve()

    @staticmethod
    def test_bad6():
        """
        FAILED  [ 37%]
Z3 formula:  Or(And(3 != 1, 2 == 3),
   And(f(2) != f(2) == (2 == 1), Not(1 != 3)))
Our formula:  (declare-fun f (Int) Int) (assert (or (and (not (= (3) (1))) (= (2) (3))) (and (<=> (not (= (f(2)) (f(2)))) (= (2) (1))) (not (not (= (1) (3)))))))

Is SAT? False
Z3:		 0.018948793411254883
Our:	 0.0009970664978027344

        """
        formula = "(declare-fun f (Int) Int) (assert (or (and (not (= (3) (1))) (= (2) (3))) (and (<=> (not (= (f(2)) (f(2)))) (= (2) (1))) (not (not (= (1) (3)))))))"
        assert UFSolver(*FormulaParser.import_uf(formula)).solve()

    @staticmethod
    def test_bad7():
        """
        Z3 formula:  Not(Implies(Not(And(And(And(Not(Or(((3 == 1) == 1 != 1) ==
                                   (2 == g(3)),
                                   (3 == 1) == (2 == g(3)))),
                            1 != 1),
                        Or(And(((3 == 1) == 1 != 1) ==
                               (2 == g(3)),
                               Or(Or((3 == 1) == (2 == g(3)),
                                     (3 == 1) == (2 == g(3))),
                                  Not(3 == 1))),
                           Implies(1 != 1, 3 == 1))),
                    Or(Or((3 == 1) == (2 == g(3)),
                          (3 == 1) == (2 == g(3))),
                       Not(Not(2 == g(3)))))),
            And(Or(Implies(Or(Or(3 == 1,
                                 Implies(((3 == 1) == 1 != 1) ==
                                        (2 == g(3)),
                                        Or(Or(((3 == 1) ==
                                        1 != 1) ==
                                        (2 == g(3)),
                                        (3 == 1) ==
                                        (2 == g(3))),
                                        Implies(Not(2 ==
                                        g(3)),
                                        Or((3 == 1) ==
                                        (2 == g(3)),
                                        (3 == 1) ==
                                        (2 == g(3))) ==
                                        Not(And(Or(((3 == 1) ==
                                        1 != 1) ==
                                        (2 == g(3)),
                                        (3 == 1) ==
                                        (2 == g(3))),
                                        Implies(1 != 1,
                                        3 == 1))))))),
                              Not(Not(Or(And(((3 == 1) ==
                                        1 != 1) ==
                                        (2 == g(3)),
                                        Or(Or((3 == 1) ==
                                        (2 == g(3)),
                                        (3 == 1) ==
                                        (2 == g(3))),
                                        Not(3 == 1))),
                                        Implies(1 != 1,
                                        3 == 1))))),
                           Implies(Implies(Not(2 == g(3)),
                                        (3 == 1) ==
                                        Not(2 == g(3))),
                                   (3 == 1) == 1 != 1)),
                   Or(Or(And(And(Not(Or(((3 == 1) == 1 != 1) ==
                                        (2 == g(3)),
                                        (3 == 1) ==
                                        (2 == g(3)))),
                                 1 != 1),
                             Or(And(((3 == 1) == 1 != 1) ==
                                    (2 == g(3)),
                                    Or(Or((3 == 1) ==
                                        (2 == g(3)),
                                        (3 == 1) ==
                                        (2 == g(3))),
                                       Not(3 == 1))),
                                Implies(1 != 1, 3 == 1))),
                         Or((3 == 1) == (2 == g(3)),
                            (3 == 1) == (2 == g(3))) ==
                         Not(And(Or(((3 == 1) == 1 != 1) ==
                                    (2 == g(3)),
                                    (3 == 1) == (2 == g(3))),
                                 Implies(1 != 1, 3 == 1)))) ==
                      Implies(Or((3 == 1) == (2 == g(3)),
                                 (3 == 1) == (2 == g(3))),
                              And(Or(((3 == 1) == 1 != 1) ==
                                     (2 == g(3)),
                                     (3 == 1) == (2 == g(3))),
                                  Implies(1 != 1, 3 == 1))),
                      Implies(Not(2 == g(3)), 2 == g(3)))),
                Implies(Not(2 == g(3)),
                        Or((3 == 1) == (2 == g(3)),
                           (3 == 1) == (2 == g(3))) ==
                        Not(And(Or(((3 == 1) == 1 != 1) ==
                                   (2 == g(3)),
                                   (3 == 1) == (2 == g(3))),
                                Implies(1 != 1, 3 == 1)))))))
Our formula:  (declare-fun f (Int) Int) (declare-fun g (Int) Int) (assert (not (=> (not (and (and (and (not (or (<=> (<=> (= (3) (1)) (not (= (1) (1)))) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3)))))) (not (= (1) (1)))) (or (and (<=> (<=> (= (3) (1)) (not (= (1) (1)))) (= (2) (g(3)))) (or (or (<=> (= (3) (1)) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3))))) (not (= (3) (1))))) (=> (not (= (1) (1))) (= (3) (1))))) (or (or (<=> (= (3) (1)) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3))))) (not (not (= (2) (g(3)))))))) (and (or (=> (or (or (= (3) (1)) (=> (<=> (<=> (= (3) (1)) (not (= (1) (1)))) (= (2) (g(3)))) (or (or (<=> (<=> (= (3) (1)) (not (= (1) (1)))) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3))))) (=> (not (= (2) (g(3)))) (<=> (or (<=> (= (3) (1)) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3))))) (not (and (or (<=> (<=> (= (3) (1)) (not (= (1) (1)))) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3))))) (=> (not (= (1) (1))) (= (3) (1)))))))))) (not (not (or (and (<=> (<=> (= (3) (1)) (not (= (1) (1)))) (= (2) (g(3)))) (or (or (<=> (= (3) (1)) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3))))) (not (= (3) (1))))) (=> (not (= (1) (1))) (= (3) (1))))))) (=> (=> (not (= (2) (g(3)))) (<=> (= (3) (1)) (not (= (2) (g(3)))))) (<=> (= (3) (1)) (not (= (1) (1)))))) (or (<=> (or (and (and (not (or (<=> (<=> (= (3) (1)) (not (= (1) (1)))) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3)))))) (not (= (1) (1)))) (or (and (<=> (<=> (= (3) (1)) (not (= (1) (1)))) (= (2) (g(3)))) (or (or (<=> (= (3) (1)) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3))))) (not (= (3) (1))))) (=> (not (= (1) (1))) (= (3) (1))))) (<=> (or (<=> (= (3) (1)) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3))))) (not (and (or (<=> (<=> (= (3) (1)) (not (= (1) (1)))) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3))))) (=> (not (= (1) (1))) (= (3) (1))))))) (=> (or (<=> (= (3) (1)) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3))))) (and (or (<=> (<=> (= (3) (1)) (not (= (1) (1)))) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3))))) (=> (not (= (1) (1))) (= (3) (1)))))) (=> (not (= (2) (g(3)))) (= (2) (g(3)))))) (=> (not (= (2) (g(3)))) (<=> (or (<=> (= (3) (1)) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3))))) (not (and (or (<=> (<=> (= (3) (1)) (not (= (1) (1)))) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3))))) (=> (not (= (1) (1))) (= (3) (1)))))))))))

Is SAT? True
Z3:		 0.009998798370361328
Our:	 0.005006551742553711
        """
        formula = "(declare-fun f (Int) Int) (declare-fun g (Int) Int) (assert (not (=> (not (and (and (and (not (or (<=> (<=> (= (3) (1)) (not (= (1) (1)))) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3)))))) (not (= (1) (1)))) (or (and (<=> (<=> (= (3) (1)) (not (= (1) (1)))) (= (2) (g(3)))) (or (or (<=> (= (3) (1)) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3))))) (not (= (3) (1))))) (=> (not (= (1) (1))) (= (3) (1))))) (or (or (<=> (= (3) (1)) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3))))) (not (not (= (2) (g(3)))))))) (and (or (=> (or (or (= (3) (1)) (=> (<=> (<=> (= (3) (1)) (not (= (1) (1)))) (= (2) (g(3)))) (or (or (<=> (<=> (= (3) (1)) (not (= (1) (1)))) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3))))) (=> (not (= (2) (g(3)))) (<=> (or (<=> (= (3) (1)) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3))))) (not (and (or (<=> (<=> (= (3) (1)) (not (= (1) (1)))) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3))))) (=> (not (= (1) (1))) (= (3) (1)))))))))) (not (not (or (and (<=> (<=> (= (3) (1)) (not (= (1) (1)))) (= (2) (g(3)))) (or (or (<=> (= (3) (1)) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3))))) (not (= (3) (1))))) (=> (not (= (1) (1))) (= (3) (1))))))) (=> (=> (not (= (2) (g(3)))) (<=> (= (3) (1)) (not (= (2) (g(3)))))) (<=> (= (3) (1)) (not (= (1) (1)))))) (or (<=> (or (and (and (not (or (<=> (<=> (= (3) (1)) (not (= (1) (1)))) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3)))))) (not (= (1) (1)))) (or (and (<=> (<=> (= (3) (1)) (not (= (1) (1)))) (= (2) (g(3)))) (or (or (<=> (= (3) (1)) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3))))) (not (= (3) (1))))) (=> (not (= (1) (1))) (= (3) (1))))) (<=> (or (<=> (= (3) (1)) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3))))) (not (and (or (<=> (<=> (= (3) (1)) (not (= (1) (1)))) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3))))) (=> (not (= (1) (1))) (= (3) (1))))))) (=> (or (<=> (= (3) (1)) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3))))) (and (or (<=> (<=> (= (3) (1)) (not (= (1) (1)))) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3))))) (=> (not (= (1) (1))) (= (3) (1)))))) (=> (not (= (2) (g(3)))) (= (2) (g(3)))))) (=> (not (= (2) (g(3)))) (<=> (or (<=> (= (3) (1)) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3))))) (not (and (or (<=> (<=> (= (3) (1)) (not (= (1) (1)))) (= (2) (g(3)))) (<=> (= (3) (1)) (= (2) (g(3))))) (=> (not (= (1) (1))) (= (3) (1)))))))))))"
        assert UFSolver(*FormulaParser.import_uf(formula)).solve()

    @staticmethod
    def test_bad8():
        """
        FAILED   [ 34%]
Z3 formula:  Not(And(Implies(Or(And(Not(Implies(3 == 1, 3 != f(3)) ==
                           Implies(3 == 1, 3 != f(3))),
                       And(Or(2 != f(1),
                              Or(Not(Implies(3 == 1,
                                        3 != f(3)) ==
                                     Implies(3 == 1,
                                        3 != f(3))),
                                 And(f(1) == 1,
                                     Implies(2 != f(1),
                                        And(1 != 2,
                                        3 != f(3)))))),
                           2 != f(1))),
                   And(And(f(1) == 1,
                           Implies(2 != f(1),
                                   And(1 != 2, 3 != f(3)))),
                       f(1) == 1) ==
                   (Implies(2 != f(1),
                            And(f(1) == 1,
                                Implies(2 != f(1),
                                        And(1 != 2,
                                        3 != f(3))))) ==
                    (f(1) == 1))),
                Implies(Or(Or(Implies(2 != f(1),
                                      And(f(1) == 1,
                                        Implies(2 != f(1),
                                        And(1 != 2,
                                        3 != f(3))))),
                              Implies(f(1) != 3, f(1) == 1)),
                           Or(Implies(Implies(f(1) != 3,
                                        f(1) == 1),
                                      Implies(f(1) == 1,
                                        Implies(3 == 1,
                                        3 != f(3)) ==
                                        Implies(3 == 1,
                                        3 != f(3)))),
                              f(1) != 3)),
                        Not(And(f(1) == 1,
                                Implies(2 != f(1),
                                        And(1 != 2,
                                        3 != f(3))))))),
        Or(Or(Or(Not(Implies(3 == 1, 3 != f(3)) ==
                     Implies(3 == 1, 3 != f(3))),
                 Not(3 == 1)),
              Or(Not(Implies(And(Implies(3 == 1, 3 != f(3)) ==
                                 Implies(3 == 1, 3 != f(3)),
                                 And(f(1) == 1,
                                     Implies(2 != f(1),
                                        And(1 != 2,
                                        3 != f(3))))),
                             1 != 2)),
                 3 != f(3))),
           And(And(Not(Implies(Implies(f(1) != 3, f(1) == 1),
                               Implies(f(1) == 1,
                                       Implies(3 == 1,
                                        3 != f(3)) ==
                                       Implies(3 == 1,
                                        3 != f(3))))),
                   Implies(f(1) != 3, f(1) == 1)) ==
               2 != f(1),
               Not(Implies(And(Implies(3 == 1, 3 != f(3)) ==
                               Implies(3 == 1, 3 != f(3)),
                               And(f(1) == 1,
                                   Implies(2 != f(1),
                                        And(1 != 2,
                                        3 != f(3))))),
                           1 != 2)) ==
               Or(Implies(f(1) == 1,
                          Implies(3 == 1, 3 != f(3)) ==
                          Implies(3 == 1, 3 != f(3))),
                  And(Implies(3 == 1, 3 != f(3)) ==
                      Implies(3 == 1, 3 != f(3)),
                      And(f(1) == 1,
                          Implies(2 != f(1),
                                  And(1 != 2, 3 != f(3))))) ==
                  And(Implies(3 == 1, 3 != f(3)) ==
                      Implies(3 == 1, 3 != f(3)),
                      And(f(1) == 1,
                          Implies(2 != f(1),
                                  And(1 != 2, 3 != f(3))))))))))
Our formula:  (declare-fun f (Int) Int) (declare-fun g (Int) Int) (assert (not (and (=> (or (and (not (<=> (=> (= (3) (1)) (not (= (3) (f(3))))) (=> (= (3) (1)) (not (= (3) (f(3))))))) (and (or (not (= (2) (f(1)))) (or (not (<=> (=> (= (3) (1)) (not (= (3) (f(3))))) (=> (= (3) (1)) (not (= (3) (f(3))))))) (and (= (f(1)) (1)) (=> (not (= (2) (f(1)))) (and (not (= (1) (2))) (not (= (3) (f(3))))))))) (not (= (2) (f(1)))))) (<=> (and (and (= (f(1)) (1)) (=> (not (= (2) (f(1)))) (and (not (= (1) (2))) (not (= (3) (f(3))))))) (= (f(1)) (1))) (<=> (=> (not (= (2) (f(1)))) (and (= (f(1)) (1)) (=> (not (= (2) (f(1)))) (and (not (= (1) (2))) (not (= (3) (f(3)))))))) (= (f(1)) (1))))) (=> (or (or (=> (not (= (2) (f(1)))) (and (= (f(1)) (1)) (=> (not (= (2) (f(1)))) (and (not (= (1) (2))) (not (= (3) (f(3)))))))) (=> (not (= (f(1)) (3))) (= (f(1)) (1)))) (or (=> (=> (not (= (f(1)) (3))) (= (f(1)) (1))) (=> (= (f(1)) (1)) (<=> (=> (= (3) (1)) (not (= (3) (f(3))))) (=> (= (3) (1)) (not (= (3) (f(3)))))))) (not (= (f(1)) (3))))) (not (and (= (f(1)) (1)) (=> (not (= (2) (f(1)))) (and (not (= (1) (2))) (not (= (3) (f(3)))))))))) (or (or (or (not (<=> (=> (= (3) (1)) (not (= (3) (f(3))))) (=> (= (3) (1)) (not (= (3) (f(3))))))) (not (= (3) (1)))) (or (not (=> (and (<=> (=> (= (3) (1)) (not (= (3) (f(3))))) (=> (= (3) (1)) (not (= (3) (f(3)))))) (and (= (f(1)) (1)) (=> (not (= (2) (f(1)))) (and (not (= (1) (2))) (not (= (3) (f(3)))))))) (not (= (1) (2))))) (not (= (3) (f(3)))))) (and (<=> (and (not (=> (=> (not (= (f(1)) (3))) (= (f(1)) (1))) (=> (= (f(1)) (1)) (<=> (=> (= (3) (1)) (not (= (3) (f(3))))) (=> (= (3) (1)) (not (= (3) (f(3))))))))) (=> (not (= (f(1)) (3))) (= (f(1)) (1)))) (not (= (2) (f(1))))) (<=> (not (=> (and (<=> (=> (= (3) (1)) (not (= (3) (f(3))))) (=> (= (3) (1)) (not (= (3) (f(3)))))) (and (= (f(1)) (1)) (=> (not (= (2) (f(1)))) (and (not (= (1) (2))) (not (= (3) (f(3)))))))) (not (= (1) (2))))) (or (=> (= (f(1)) (1)) (<=> (=> (= (3) (1)) (not (= (3) (f(3))))) (=> (= (3) (1)) (not (= (3) (f(3))))))) (<=> (and (<=> (=> (= (3) (1)) (not (= (3) (f(3))))) (=> (= (3) (1)) (not (= (3) (f(3)))))) (and (= (f(1)) (1)) (=> (not (= (2) (f(1)))) (and (not (= (1) (2))) (not (= (3) (f(3)))))))) (and (<=> (=> (= (3) (1)) (not (= (3) (f(3))))) (=> (= (3) (1)) (not (= (3) (f(3)))))) (and (= (f(1)) (1)) (=> (not (= (2) (f(1)))) (and (not (= (1) (2))) (not (= (3) (f(3))))))))))))))))


conflict_clause = {-25, -21, -18, 10}

    def _conflict_resolution(self, conflict_clause):
        Learns conflict clauses using implication graphs, with the Unique Implication Point heuristic.

        conflict_clause = set(conflict_clause)
        while True:
            last_literal, prev_max_level, max_level, max_idx, max_level_count = None, -1, -1, -1, 0
            for literal in conflict_clause:
                variable = abs(literal)
                # if variable not in self._assignment:
                #     continue
>               level, idx = self._assignment[variable]["level"], self._assignment[variable]["idx"]
E               KeyError: 25
        """
        formula = "(declare-fun f (Int) Int) (declare-fun g (Int) Int) (assert (not (and (=> (or (and (not (<=> (=> (= (3) (1)) (not (= (3) (f(3))))) (=> (= (3) (1)) (not (= (3) (f(3))))))) (and (or (not (= (2) (f(1)))) (or (not (<=> (=> (= (3) (1)) (not (= (3) (f(3))))) (=> (= (3) (1)) (not (= (3) (f(3))))))) (and (= (f(1)) (1)) (=> (not (= (2) (f(1)))) (and (not (= (1) (2))) (not (= (3) (f(3))))))))) (not (= (2) (f(1)))))) (<=> (and (and (= (f(1)) (1)) (=> (not (= (2) (f(1)))) (and (not (= (1) (2))) (not (= (3) (f(3))))))) (= (f(1)) (1))) (<=> (=> (not (= (2) (f(1)))) (and (= (f(1)) (1)) (=> (not (= (2) (f(1)))) (and (not (= (1) (2))) (not (= (3) (f(3)))))))) (= (f(1)) (1))))) (=> (or (or (=> (not (= (2) (f(1)))) (and (= (f(1)) (1)) (=> (not (= (2) (f(1)))) (and (not (= (1) (2))) (not (= (3) (f(3)))))))) (=> (not (= (f(1)) (3))) (= (f(1)) (1)))) (or (=> (=> (not (= (f(1)) (3))) (= (f(1)) (1))) (=> (= (f(1)) (1)) (<=> (=> (= (3) (1)) (not (= (3) (f(3))))) (=> (= (3) (1)) (not (= (3) (f(3)))))))) (not (= (f(1)) (3))))) (not (and (= (f(1)) (1)) (=> (not (= (2) (f(1)))) (and (not (= (1) (2))) (not (= (3) (f(3)))))))))) (or (or (or (not (<=> (=> (= (3) (1)) (not (= (3) (f(3))))) (=> (= (3) (1)) (not (= (3) (f(3))))))) (not (= (3) (1)))) (or (not (=> (and (<=> (=> (= (3) (1)) (not (= (3) (f(3))))) (=> (= (3) (1)) (not (= (3) (f(3)))))) (and (= (f(1)) (1)) (=> (not (= (2) (f(1)))) (and (not (= (1) (2))) (not (= (3) (f(3)))))))) (not (= (1) (2))))) (not (= (3) (f(3)))))) (and (<=> (and (not (=> (=> (not (= (f(1)) (3))) (= (f(1)) (1))) (=> (= (f(1)) (1)) (<=> (=> (= (3) (1)) (not (= (3) (f(3))))) (=> (= (3) (1)) (not (= (3) (f(3))))))))) (=> (not (= (f(1)) (3))) (= (f(1)) (1)))) (not (= (2) (f(1))))) (<=> (not (=> (and (<=> (=> (= (3) (1)) (not (= (3) (f(3))))) (=> (= (3) (1)) (not (= (3) (f(3)))))) (and (= (f(1)) (1)) (=> (not (= (2) (f(1)))) (and (not (= (1) (2))) (not (= (3) (f(3)))))))) (not (= (1) (2))))) (or (=> (= (f(1)) (1)) (<=> (=> (= (3) (1)) (not (= (3) (f(3))))) (=> (= (3) (1)) (not (= (3) (f(3))))))) (<=> (and (<=> (=> (= (3) (1)) (not (= (3) (f(3))))) (=> (= (3) (1)) (not (= (3) (f(3)))))) (and (= (f(1)) (1)) (=> (not (= (2) (f(1)))) (and (not (= (1) (2))) (not (= (3) (f(3)))))))) (and (<=> (=> (= (3) (1)) (not (= (3) (f(3))))) (=> (= (3) (1)) (not (= (3) (f(3)))))) (and (= (f(1)) (1)) (=> (not (= (2) (f(1)))) (and (not (= (1) (2))) (not (= (3) (f(3))))))))))))))))"
        assert UFSolver(*FormulaParser.import_uf(formula)).solve()

    @staticmethod
    def test_bad9():
        """
        FAILED [ 80%]
Z3 formula:  And((2 == 1) ==
    ((3 == f(2)) == Or((2 == 1) == (1 == f(2)), 1 == f(2))),
    Not(And(2 == 3, 3 == f(2))))
Our formula:  (declare-fun f (Int) Int) (declare-fun g (Int) Int) (assert (and (<=> (= (2) (1)) (<=> (= (3) (f(2))) (or (<=> (= (2) (1)) (= (1) (f(2)))) (= (1) (f(2)))))) (not (and (= (2) (3)) (= (3) (f(2)))))))
        """
        formula = "(declare-fun f (Int) Int) (declare-fun g (Int) Int) (assert (and (<=> (= (2) (1)) (<=> (= (3) (f(2))) (or (<=> (= (2) (1)) (= (1) (f(2)))) (= (1) (f(2)))))) (not (and (= (2) (3)) (= (3) (f(2)))))))"
        assert UFSolver(*FormulaParser.import_uf(formula)).solve()

    @staticmethod
    def test_bad10():
        """
        FAILED [ 96%]
Z3 formula:  Or(f(1) != 1 == (g(f(1)) == g(1)),
   And(Not(3 != f(1)),
       Implies(Not(3 != f(1)), And(3 != f(1), f(1) != 1))))
Our formula:  (declare-fun f (Int) Int) (declare-fun g (Int) Int) (assert (or (<=> (not (= (f(1)) (1))) (= (g(f(1))) (g(1)))) (and (not (not (= (3) (f(1))))) (=> (not (not (= (3) (f(1))))) (and (not (= (3) (f(1)))) (not (= (f(1)) (1))))))))

Is SAT? True
Z3:		 0.014582395553588867
Our:	 0.0025734901428222656
        """
        formula = "(declare-fun f (Int) Int) (declare-fun g (Int) Int) (assert (or (<=> (not (= (f(1)) (1))) (= (g(f(1))) (g(1)))) (and (not (not (= (3) (f(1))))) (=> (not (not (= (3) (f(1))))) (and (not (= (3) (f(1)))) (not (= (f(1)) (1))))))))"
        assert UFSolver(*FormulaParser.import_uf(formula)).solve()

    @staticmethod
    def test_bad11():
        """
        FAILED [ 84%]
Z3 formula:  3 != g(3) ==
And(Implies(g(3) == g(g(g(3))), g(g(3)) == 3),
    (g(g(g(3))) == g(g(g(3)))) ==
    Or(g(3) == g(g(g(3))), g(g(3)) == 3))
Our formula:  (declare-fun f (Int) Int) (declare-fun g (Int) Int) (assert (<=> (not (= (3) (g(3)))) (and (=> (= (g(3)) (g(g(g(3))))) (= (g(g(3))) (3))) (<=> (= (g(g(g(3)))) (g(g(g(3))))) (or (= (g(3)) (g(g(g(3))))) (= (g(g(3))) (3)))))))

Is SAT? True
Z3:		 0.01025700569152832
Our:	 0.00821232795715332

        """
        Not, And, Or, Implies = z3.Not, z3.And, z3.Or, z3.Implies
        f, g = z3.Function('f', z3.IntSort(), z3.IntSort()), z3.Function('g', z3.IntSort(), z3.IntSort())
        x1, x2, x3 = z3.Int("x1"), z3.Int("x2"), z3.Int("x3")
        z3_solver = z3.Solver()
        z3_solver.add((x3 != g(x3)) ==
                      And(Implies(g(x3) == g(g(g(x3))), g(g(x3)) == x3),
                          (g(g(g(x3))) == g(g(g(x3)))) ==
                          Or(g(x3) == g(g(g(x3))), g(g(x3)) == x3)))
        print(z3_solver.check())
        formula = "(declare-fun f (Int) Int) (declare-fun g (Int) Int) (assert (<=> (not (= (3) (g(3)))) (and (=> (= (g(3)) (g(g(g(3))))) (= (g(g(3))) (3))) (<=> (= (g(g(g(3)))) (g(g(g(3))))) (or (= (g(3)) (g(g(g(3))))) (= (g(g(3))) (3)))))))"
        assert UFSolver(*FormulaParser.import_uf(formula)).solve() == (z3_solver.check() == z3.sat)

    @staticmethod
    def test_bad13():
        """
        FAILED [ 84%]
Z3 formula:  And(And(f(3) == f(2), And(f(2) != g(f(3)), f(2) != g(f(2)))) ==
    Not(f(2) != g(f(3))),
    And(f(3) == f(2),
        Not(f(2) != g(f(3))) == f(2) != g(f(2))))
Our formula:  (declare-fun f (Int) Int) (declare-fun g (Int) Int) (assert (and (<=> (and (= (f(3)) (f(2))) (and (not (= (f(2)) (g(f(3))))) (not (= (f(2)) (g(f(2))))))) (not (not (= (f(2)) (g(f(3))))))) (and (= (f(3)) (f(2))) (<=> (not (not (= (f(2)) (g(f(3)))))) (not (= (f(2)) (g(f(2)))))))))

Is SAT? False
Z3:		 0.015210628509521484
Our:	 0.0025670528411865234

        """
        formula = "(declare-fun f (Int) Int) (declare-fun g (Int) Int) (assert (and (<=> (and (= (f(3)) (f(2))) (and (not (= (f(2)) (g(f(3))))) (not (= (f(2)) (g(f(2))))))) (not (not (= (f(2)) (g(f(3))))))) (and (= (f(3)) (f(2))) (<=> (not (not (= (f(2)) (g(f(3)))))) (not (= (f(2)) (g(f(2)))))))))"
        assert not UFSolver(*FormulaParser.import_uf(formula)).solve()

    @staticmethod
    def test_bad14():
        """
        FAILED  [ 53%]
Z3 formula:  Not(And(Implies(1 == 2, Implies(3 != 1 == (2 == 3), 3 != 1)),
        Or(And(And(3 == 1, 3 == 1),
               And(1 == 2, 2 == 3) ==
               Implies(3 != 1 == (2 == 3), 3 != 1)),
           Implies((1 == 2) == 3 != 1,
                   Implies(Implies((1 == 2) == 3 != 1,
                                   2 == 3),
                           1 == 2)))))
Our formula:  (declare-fun f (Int) Int) (declare-fun g (Int) Int) (assert (not (and (=> (= (1) (2)) (=> (<=> (not (= (3) (1))) (= (2) (3))) (not (= (3) (1))))) (or (and (and (= (3) (1)) (= (3) (1))) (<=> (and (= (1) (2)) (= (2) (3))) (=> (<=> (not (= (3) (1))) (= (2) (3))) (not (= (3) (1)))))) (=> (<=> (= (1) (2)) (not (= (3) (1)))) (=> (=> (<=> (= (1) (2)) (not (= (3) (1)))) (= (2) (3))) (= (1) (2))))))))

Is SAT? False
Z3:		 0.020142793655395508
Our:	 0.0
        """
        formula = "(declare-fun f (Int) Int) (declare-fun g (Int) Int) (assert (not (and (=> (= (1) (2)) (=> (<=> (not (= (3) (1))) (= (2) (3))) (not (= (3) (1))))) (or (and (and (= (3) (1)) (= (3) (1))) (<=> (and (= (1) (2)) (= (2) (3))) (=> (<=> (not (= (3) (1))) (= (2) (3))) (not (= (3) (1)))))) (=> (<=> (= (1) (2)) (not (= (3) (1)))) (=> (=> (<=> (= (1) (2)) (not (= (3) (1)))) (= (2) (3))) (= (1) (2))))))))"
        assert not UFSolver(*FormulaParser.import_uf(formula)).solve()

    @staticmethod
    def test_bad15():
        """
        Z3 formula:  Implies(Or(((x2 == g(g(x3))) == x1 != g(x3)) ==
           (x3 == g(x3)),
           Or(x3 == g(x3), g(x3) != g(x3))),
        Not(Or(Implies(Or(x3 == g(x3), g(x3) != g(x3)) ==
                       x1 != g(x3),
                       Or(x1 != g(x3) ==
                          ((x2 == g(g(x3))) == Not(x3 != x2)),
                          Implies(Or(g(x3) != g(x3),
                                     x2 == g(g(x3))),
                                  Or(x3 == g(x3),
                                     g(x3) != g(x3))))),
               Or(x1 != g(x3), Not(x3 != x2)))))
Our formula:  (declare-fun f (Int) Int) (declare-fun g (Int) Int) (assert (=> (or (<=> (<=> (= (x2) (g(g(x3)))) (not (= (x1) (g(x3))))) (= (x3) (g(x3)))) (or (= (x3) (g(x3))) (not (= (g(x3)) (g(x3)))))) (not (or (=> (<=> (or (= (x3) (g(x3))) (not (= (g(x3)) (g(x3))))) (not (= (x1) (g(x3))))) (or (<=> (not (= (x1) (g(x3)))) (<=> (= (x2) (g(g(x3)))) (not (not (= (x3) (x2)))))) (=> (or (not (= (g(x3)) (g(x3)))) (= (x2) (g(g(x3))))) (or (= (x3) (g(x3))) (not (= (g(x3)) (g(x3)))))))) (or (not (= (x1) (g(x3)))) (not (not (= (x3) (x2)))))))))

Is SAT? False
Z3:		 0.017950773239135742
Our:	 0.001993894577026367
        """
        formula = "(declare-fun f (Int) Int) (declare-fun g (Int) Int) (assert (=> (or (<=> (<=> (= (x2) (g(g(x3)))) (not (= (x1) (g(x3))))) (= (x3) (g(x3)))) (or (= (x3) (g(x3))) (not (= (g(x3)) (g(x3)))))) (not (or (=> (<=> (or (= (x3) (g(x3))) (not (= (g(x3)) (g(x3))))) (not (= (x1) (g(x3))))) (or (<=> (not (= (x1) (g(x3)))) (<=> (= (x2) (g(g(x3)))) (not (not (= (x3) (x2)))))) (=> (or (not (= (g(x3)) (g(x3)))) (= (x2) (g(g(x3))))) (or (= (x3) (g(x3))) (not (= (g(x3)) (g(x3)))))))) (or (not (= (x1) (g(x3)))) (not (not (= (x3) (x2)))))))))"
        assert not UFSolver(*FormulaParser.import_uf(formula)).solve()

    @staticmethod
    def test_bad16():
        """
        Z3 formula:  Or(Not(Or(Or(And(Implies(Implies(g(x1) == x2, g(x1) != x3),
                         Implies(g(x1) == x2, g(x1) != x3)),
                 Implies(g(x1) == x2, g(x1) != x3)),
             And(Implies(Implies(g(x1) == x2, g(x1) != x3),
                         Implies(g(x1) == x2, g(x1) != x3)),
                 Implies(g(x1) == x2, g(x1) != x3))) ==
          Implies(f(x1) == x1,
                  And(Implies(Implies(g(x1) == x2,
                                      g(x1) != x3),
                              Implies(g(x1) == x2,
                                      g(x1) != x3)),
                      Implies(g(x1) == x2, g(x1) != x3))),
          Implies(f(x1) == x1,
                  And(Implies(Implies(g(x1) == x2,
                                      g(x1) != x3),
                              Implies(g(x1) == x2,
                                      g(x1) != x3)),
                      Implies(g(x1) == x2, g(x1) != x3))))),
   Or(And(Implies(Implies(g(x1) == x2, g(x1) != x3),
                  Implies(g(x1) == x2, g(x1) != x3)),
          Implies(g(x1) == x2, g(x1) != x3)),
      And(Implies(Implies(g(x1) == x2, g(x1) != x3),
                  Implies(g(x1) == x2, g(x1) != x3)),
          Implies(g(x1) == x2, g(x1) != x3))))
Our formula:  (declare-fun f (Int) Int) (declare-fun g (Int) Int) (assert (or (not (or (<=> (or (and (=> (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3)))) (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3))))) (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3))))) (and (=> (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3)))) (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3))))) (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3)))))) (=> (= (f(x1)) (x1)) (and (=> (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3)))) (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3))))) (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3))))))) (=> (= (f(x1)) (x1)) (and (=> (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3)))) (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3))))) (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3)))))))) (or (and (=> (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3)))) (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3))))) (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3))))) (and (=> (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3)))) (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3))))) (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3))))))))

Is SAT? False
Z3:		 0.01995706558227539
Our:	 0.001994609832763672
        """
        formula = "(declare-fun f (Int) Int) (declare-fun g (Int) Int) (assert (or (not (or (<=> (or (and (=> (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3)))) (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3))))) (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3))))) (and (=> (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3)))) (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3))))) (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3)))))) (=> (= (f(x1)) (x1)) (and (=> (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3)))) (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3))))) (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3))))))) (=> (= (f(x1)) (x1)) (and (=> (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3)))) (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3))))) (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3)))))))) (or (and (=> (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3)))) (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3))))) (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3))))) (and (=> (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3)))) (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3))))) (=> (= (g(x1)) (x2)) (not (= (g(x1)) (x3))))))))"
        assert not UFSolver(*FormulaParser.import_uf(formula)).solve()

    @staticmethod
    def test_bad17():
        """
        Z3 formula:  Or(Or(Or(x3 == x2, x1 != x2),
      Not(Or(Or(x1 != x2, x3 == x2), x1 != x2))),
   Or(x3 == x2, Or(x3 == x1, x3 == x2)) == (x3 == f(f(x1)))) ==
(x1 != x2 ==
 Implies(Or(Or(x1 != x2, x3 == x2), x1 != x2),
         Or(x1 != x2, x3 == x2)))
Our formula:  (declare-fun f (Int) Int) (declare-fun g (Int) Int) (assert (<=> (or (or (or (= (x3) (x2)) (not (= (x1) (x2)))) (not (or (or (not (= (x1) (x2))) (= (x3) (x2))) (not (= (x1) (x2)))))) (<=> (or (= (x3) (x2)) (or (= (x3) (x1)) (= (x3) (x2)))) (= (x3) (f(f(x1)))))) (<=> (not (= (x1) (x2))) (=> (or (or (not (= (x1) (x2))) (= (x3) (x2))) (not (= (x1) (x2)))) (or (not (= (x1) (x2))) (= (x3) (x2)))))))

Is SAT? True
Z3:		 0.016955137252807617
Our:	 0.0009975433349609375
        """
        formula = "(declare-fun f (Int) Int) (declare-fun g (Int) Int) (assert (<=> (or (or (or (= (x3) (x2)) (not (= (x1) (x2)))) (not (or (or (not (= (x1) (x2))) (= (x3) (x2))) (not (= (x1) (x2)))))) (<=> (or (= (x3) (x2)) (or (= (x3) (x1)) (= (x3) (x2)))) (= (x3) (f(f(x1)))))) (<=> (not (= (x1) (x2))) (=> (or (or (not (= (x1) (x2))) (= (x3) (x2))) (not (= (x1) (x2)))) (or (not (= (x1) (x2))) (= (x3) (x2)))))))"
        assert UFSolver(*FormulaParser.import_uf(formula)).solve()

    @staticmethod
    @pytest.mark.parametrize("variable_num, operator_num, function_num",
                             [(3, operator_num, 1) for operator_num in list(range(10, 50))])
    def test_random_uf_equations(variable_num: int, operator_num: int, function_num: int):
        equations_z3, equations_our_txt, equations_our = \
            TestUFSolver.generate_random_equations(variable_num, operator_num, function_num)
        if not equations_z3:
            return
        try:    # Might be the case that the formula is not valid
            formula_z3 = z3.And(equations_z3)
        except z3.Z3Exception:
            return
        formula_our_txt = "(declare-fun f (Int) Int) (declare-fun g (Int) Int) " + \
                          ' '.join(["(assert (" + eq + "))" for eq in equations_our_txt])
        print()
        print("Z3 formula: ", formula_z3)
        print("Our formula: ", formula_our_txt)
        assert TestSATSolver.compare_to_z3(formula_z3, UFSolver(*FormulaParser.import_uf(formula_our_txt)))

    @staticmethod
    @pytest.mark.parametrize("variable_num, operator_num, function_num",
                             [(3, clause_num, 2) for clause_num in list(range(10, 50))])
    def test_random_uf_formula(variable_num: int, operator_num: int, function_num: int):
        equations_z3, equations_our_txt, equations_our = \
            TestUFSolver.generate_random_equations(variable_num, 10, function_num)
        if not equations_z3:
            return
        try:    # Might be the case that the formula is not valid
            formula_z3, formula_our_txt, formula_our = \
                TestSATSolver.generate_random_formula(0, operator_num, equations_z3, equations_our_txt, equations_our)
        except z3.Z3Exception:
            return
        formula_our_txt = "(declare-fun f (Int) Int) (declare-fun g (Int) Int) (assert (" + formula_our_txt + "))"
        print()
        print("Z3 formula: ", formula_z3)
        print("Our formula: ", formula_our_txt)
        assert TestSATSolver.compare_to_z3(formula_z3, UFSolver(*FormulaParser.import_uf(formula_our_txt)))
