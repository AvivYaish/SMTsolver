import pytest
from sat_solver.sat_solver import SATSolver
from itertools import combinations
from scipy.special import comb
import z3
import random
import numpy
import time

COLORING_BASIC_EDGES = [
    (1, 2), (1, 3), (1, 4), (1, 9), (1, 12),
    (2, 3), (2, 4), (2, 5), (2, 6),
    (3, 6), (3, 10), (3, 12),
    (4, 5), (4, 7), (4, 9),
    (5, 6), (5, 7), (5, 8),
    (6, 8), (6, 10),
    (7, 8), (7, 9), (7, 11),
    (8, 10), (8, 11),
    (9, 11), (9, 12),
    (10, 11), (10, 12),
    (11, 12)
]

COLORING_MANY_EDGES = [
    (1, 2), (1, 3), (1, 4), (1, 9), (1, 12),
    (2, 3), (2, 4), (2, 5), (2, 6),
    (3, 6), (3, 10), (3, 12),
    (4, 5), (4, 7), (4, 9),
    (5, 6), (5, 7), (5, 8),
    (6, 8), (6, 10),
    (7, 8), (7, 9), (7, 11),
    (8, 10), (8, 11),
    (9, 11), (9, 12),
    (10, 11), (10, 12),
    (11, 12),
    (13, 1), (13, 2), (13, 3), (13, 4), (13, 4), (13, 5), (13, 6), (13, 7), (13, 8), (13, 9),
    (14, 10), (14, 11), (14, 12), (14, 13),
    (15, 5),
    (16, 10), (16, 2),
    (17, 15),
    (18, 8), (18, 11),
    (19, 3),
    (20, 7),
    (21, 11),
    (22, 16),
    (23, 15), (23, 22),
    (24, 20), (24, 19), (24, 21),
    (25, 9), (25, 11), (25, 17),
    (26, 21), (26, 17),
    (27, 22),
    (28, 27),
    (29, 28),
    (30, 29),
    (31, 30),
    (32, 31),
    (33, 32),
    (34, 33),
    (35, 34),
    (36, 35),
    (37, 36),
    (38, 37),
    (39, 38),
    (40, 39),
    (41, 40),
    (42, 41),
    (43, 42),
    (44, 43),
    (45, 44),
    (46, 45), (46, 44), (46, 43), (46, 42), (46, 41), (46, 40),
]


class TestSATSolver:

    @staticmethod
    def test_prepare_formula():
        assert SATSolver._prepare_formula('         ') == ''
        assert SATSolver._prepare_formula('(((a)))') == 'a'
        assert SATSolver._prepare_formula('   and    a     b    ') == 'and a b'
        assert SATSolver._prepare_formula('   (   and a b     )     ') == 'and a b'
        assert SATSolver._prepare_formula('(and (a) (b))') == 'and (a) (b)'
        assert SATSolver._prepare_formula('and (a) (b)') == 'and (a) (b)'
        assert SATSolver._prepare_formula('(((and (a) (b))))') == 'and (a) (b)'

    @staticmethod
    def test_parse_formula():
        assert SATSolver._parse_formula("not (=> (not (and p q)) (not r))") == \
               ("not", ("=>", ("not", ("and", ("p"), ("q"))), ("not", ("r"))))
        assert SATSolver._parse_formula("not (=> (not (and pq78 q)) (not r))") == \
               ("not", ("=>", ("not", ("and", ("pq78"), ("q"))), ("not", ("r"))))
        assert SATSolver._parse_formula("not (=> (not (and ((p)) q)) ((not (r))))") == \
               ("not", ("=>", ("not", ("and", ("p"), ("q"))), ("not", ("r"))))
        assert SATSolver._parse_formula("not (=> (not (and ((p)) ((not ((((r)))))))) ((not (r))))") == \
               ("not", ("=>", ("not", ("and", ("p"), ("not", ("r")))), ("not", ("r"))))

    @staticmethod
    def test_tseitin_transform():
        transformed_formula = {
            frozenset({2, 3}),
            frozenset({1, 2}),
            frozenset({-8, -7, 6}),
            frozenset({4, 5}),
            frozenset({-6, -3}),
            frozenset({3, 6}),
            frozenset({4, -3, -2}),
            frozenset({-1, -2}),
            frozenset({8, -6}),
            frozenset({-5, -4}),
            frozenset({-6, 7}),
            frozenset({1}),
            frozenset({2, -4})
        }
        assert SATSolver._tseitin_transform(SATSolver._parse_formula("not (=> (not (and p q)) (not r))")) == \
               transformed_formula
        assert SATSolver._tseitin_transform(SATSolver._parse_formula("not (=> (not (and pq78 q)) (not r))")) == \
               transformed_formula
        assert SATSolver._tseitin_transform(SATSolver._parse_formula("and (not x) x")) == {
            frozenset({1}),
            frozenset({1, -3, -2}),
            frozenset({2, 3}),
            frozenset({3, -1}),
            frozenset({2, -1}),
            frozenset({-3, -2})
        }

    @staticmethod
    def test_preprocessing():
        assert SATSolver._preprocessing(frozenset({frozenset({})})) == frozenset()
        assert SATSolver._preprocessing(frozenset({frozenset({1})})) == frozenset({frozenset({1})})
        assert SATSolver._preprocessing(frozenset({frozenset({1}), frozenset({2})})) == \
               frozenset({frozenset({2}), frozenset({1})})
        assert SATSolver._preprocessing(frozenset({frozenset({2, 1}), frozenset({3, 4})})) == \
               frozenset({frozenset({3, 4}), frozenset({1, 2})})
        assert SATSolver._preprocessing(frozenset({frozenset({1, 2, 1, 1, 2}), frozenset({3, 4})})) == \
               frozenset({frozenset({3, 4}), frozenset({1, 2})})
        assert SATSolver._preprocessing(frozenset({frozenset({1, 2, 1, 1, 2, -1}), frozenset({3, 4})})) == \
               frozenset({frozenset({3, 4})})
        assert SATSolver._preprocessing(frozenset({frozenset({1, -1}), frozenset({3, -4})})) == \
               frozenset({frozenset({3, -4})})
        assert SATSolver._preprocessing(frozenset({frozenset({2, 1, -1}), frozenset({3, -4})})) == \
               frozenset({frozenset({3, -4})})
        assert SATSolver._preprocessing(frozenset({frozenset({1, 2, -1}), frozenset({3, -4})})) == \
               frozenset({frozenset({3, -4})})
        assert SATSolver._preprocessing(frozenset({frozenset({1, -1, 2}), frozenset({3, -4})})) == \
               frozenset({frozenset({3, -4})})
        assert SATSolver._preprocessing(frozenset({frozenset({1, 1, 2, 3, 3, -4}), frozenset({3, -4, 1, 2})})) == \
               frozenset({frozenset({1, 2, 3, -4})})

    @staticmethod
    def test_satisfy_unit_clauses():
        clause1 = frozenset({1})
        solver = SATSolver({clause1})
        solver._satisfy_unit_clauses()
        assert solver._assignment == {1: {'value': True, 'clause': clause1, 'level': 0, 'idx': 0}}

        clause2 = frozenset({1, 2})
        solver = SATSolver({clause1, clause2})
        solver._satisfy_unit_clauses()
        assert solver._assignment == {1: {'value': True, 'clause': clause1, 'level': 0, 'idx': 0}}

    @staticmethod
    def test_bcp():
        solver = SATSolver()
        solver._satisfy_unit_clauses()
        assert solver._bcp() is None
        assert solver._assignment == {}

        clause1 = frozenset({1})
        solver = SATSolver({clause1})
        solver._satisfy_unit_clauses()
        assert solver._bcp() is None

        clause2 = frozenset({1, 2})
        solver = SATSolver({clause1, clause2})
        solver._satisfy_unit_clauses()
        assert solver._bcp() is None
        assert solver._assignment == {1: {"value": True, "clause": clause1, "level": 0, "idx": 0}}

        clause3 = frozenset({-1, 2})
        solver = SATSolver({clause1, clause3})
        solver._satisfy_unit_clauses()
        assert solver._bcp() is None
        assert solver._assignment == {
            1: {"value": True, "clause": clause1, "level": 0, "idx": 0},
            2: {"value": True, "clause": clause3, "level": 0, "idx": 1}
        }

        clause4 = frozenset({-2})
        solver = SATSolver({clause1, clause3, clause4})
        solver._satisfy_unit_clauses()
        assert solver._bcp() == clause3

        clause5 = frozenset({-1, -2})
        solver = SATSolver({clause1, clause3, clause5})
        solver._satisfy_unit_clauses()
        assert solver._bcp() == clause5

        clause1 = frozenset({-1, -4, 5})
        clause2 = frozenset({-4, 6})
        clause3 = frozenset({-5, -6, 7})
        clause4 = frozenset({-7, 8})
        clause5 = frozenset({-2, -7, 9})
        clause6 = frozenset({-8, -9})
        clause7 = frozenset({-8, 9})
        formula = {clause1, clause2, clause3, clause4, clause5, clause6, clause7}
        assignment = {
            1: {"value": True, "clause": None, "level": 1, "idx": 1},
            2: {"value": True, "clause": None, "level": 2, "idx": 1},
            3: {"value": True, "clause": None, "level": 3, "idx": 1},
            4: {"value": True, "clause": None, "level": 4, "idx": 1},
        }
        solver = SATSolver(formula)
        solver._assignment = assignment
        solver._assignment_by_level = [[], [1], [2], [3], [4]]
        solver._last_assigned_literals.append(-4)
        solver._literal_to_watched_clause[-4] = {clause1, clause2}
        solver._literal_to_watched_clause[-5] = {clause3}
        solver._literal_to_watched_clause[-6] = {clause3}
        solver._literal_to_watched_clause[-7] = {clause4, clause5}
        solver._literal_to_watched_clause[-8] = {clause6}
        solver._literal_to_watched_clause[-9] = {clause6}
        solver._satisfy_unit_clauses()
        assert solver._bcp() == clause6

    @staticmethod
    def test_conflict_resolution():
        clause1 = frozenset({1})
        clause3 = frozenset({-1, 2})
        clause5 = frozenset({-1, -2})
        solver = SATSolver({clause1, clause3, clause5})
        solver._satisfy_unit_clauses()
        assert solver._conflict_resolution(solver._bcp()) == (frozenset({-1}), -1, -1)

        clause1 = frozenset({-1, -4, 5})
        clause2 = frozenset({-4, 6})
        clause3 = frozenset({-5, -6, 7})
        clause4 = frozenset({-7, 8})
        clause5 = frozenset({-2, -7, 9})
        clause6 = frozenset({-8, -9})
        clause7 = frozenset({-8, 9})
        formula = {clause1, clause2, clause3, clause4, clause5, clause6, clause7}
        assignment = {
            1: {"value": True, "clause": None, "level": 1, "idx": 1},
            2: {"value": True, "clause": None, "level": 2, "idx": 1},
            3: {"value": True, "clause": None, "level": 3, "idx": 1},
            4: {"value": True, "clause": None, "level": 4, "idx": 1},
        }
        solver = SATSolver(formula)
        solver._assignment = assignment
        solver._assignment_by_level = [[], [1], [2], [3], [4]]
        solver._last_assigned_literals.append(-4)
        solver._literal_to_watched_clause[-4] = {clause1, clause2}
        solver._literal_to_watched_clause[-5] = {clause3}
        solver._literal_to_watched_clause[-6] = {clause3}
        solver._literal_to_watched_clause[-7] = {clause4, clause5}
        solver._literal_to_watched_clause[-8] = {clause6}
        solver._literal_to_watched_clause[-9] = {clause6}
        solver._satisfy_unit_clauses()
        assert solver._conflict_resolution(solver._bcp()) == (frozenset({-7, -2}), -7, 2)

    @staticmethod
    def test_solve():
        assert SATSolver().solve()

        clause1 = frozenset({1})
        assert SATSolver({clause1}).solve()

        clause2 = frozenset({-1})
        assert not SATSolver({clause1, clause2}).solve()

        clause3 = frozenset({1, 2})
        assert SATSolver({clause1, clause3}).solve()

        clause4 = frozenset({-1, 2})
        assert SATSolver({clause1, clause4}).solve()

        clause5 = frozenset({-1, 2, -2})
        assert SATSolver({clause1, clause5}).solve()

        assert SATSolver({clause1, clause3, clause4, clause5}).solve()

        clause1 = frozenset({-1, -4, 5})
        clause2 = frozenset({-4, 6})
        clause3 = frozenset({-5, -6, 7})
        clause4 = frozenset({-7, 8})
        clause5 = frozenset({-2, -7, 9})
        clause6 = frozenset({-8, -9})
        clause7 = frozenset({-8, 9})
        solver = SATSolver({clause1, clause2, clause3, clause4, clause5, clause6, clause7})
        assert solver.solve()
        assert solver.get_assignment() == {4: False, 6: False, 7: False, 8: False, 9: True}

        clause1 = frozenset({5, -1, 3})
        clause2 = frozenset({-1, -5})
        clause3 = frozenset({-3, -4})
        clause4 = frozenset({1, 4})
        clause5 = frozenset({1, -4})
        clause6 = frozenset({-1, 5})
        assert not SATSolver({clause1, clause2, clause3, clause4, clause5, clause6}).solve()

    @staticmethod
    def generate_coloring_clauses(color_num, edges):
        colors = list(range(1, color_num + 1))
        vertices = set()
        for edge in edges:
            v1, v2 = edge
            vertices.add(v1)
            vertices.add(v2)

        variable_count = len(colors) * len(vertices)
        clause_count = len(vertices) + len(vertices) * int(comb(len(colors), 2)) + len(edges) * len(colors)
        print("Variables: ", variable_count, ", clauses: ", clause_count)

        # For every vertex v and color c there is a variable V_{v,c}.
        # Assume they are ordered, first by vertex then by color.
        # The variable corresponding to V_{v,c} is ((v-1)*len(colors) + c)
        # So: 1 is V_{1,1}, 2 is V_{1,2}, ..., c is V_{1,c}, c+1 is V_{2,1}, etc'

        vertices_are_colored = [
            (
                frozenset({
                    ((v - 1) * len(colors) + c)
                    for c in colors
                })
            )
            for v in vertices
        ]

        one_color_per_vertex = list([
            (
                list(
                    frozenset({(-((v - 1) * len(colors) + c1)),
                               (-((v - 1) * len(colors) + c2))})
                    for c1, c2 in combinations(colors, 2)
                )
            )
            for v in vertices
        ])
        one_color_per_vertex = [item for sublist in one_color_per_vertex for item in sublist]

        different_colors_per_edge = list([
            (
                list(
                    frozenset({(-((v - 1) * len(colors) + c)),
                               (-((u - 1) * len(colors) + c))})
                    for c in colors
                )
            )
            for v, u in edges
        ])
        different_colors_per_edge = [item for sublist in different_colors_per_edge for item in sublist]

        all_clauses = []
        all_clauses.extend(vertices_are_colored)
        all_clauses.extend(one_color_per_vertex)
        all_clauses.extend(different_colors_per_edge)
        all_clauses = frozenset(clause for clause in all_clauses)

        return all_clauses

    @staticmethod
    @pytest.mark.parametrize("color_num, edges, is_sat",
                             [(color_num, COLORING_BASIC_EDGES, (color_num >= 4)) for color_num in range(1, 11)])
    def test_coloring_basic(color_num: int, edges, is_sat: bool):
        # When colors are 1 ... 300:
        # Variables:  3588 , clauses:  543594
        # Ran in 16.648s
        # When colors are 1 ... 500:
        # Variables:  5988 , clauses:  1505994
        # Ran in 49.422s
        assert SATSolver(TestSATSolver.generate_coloring_clauses(color_num, edges)).solve() is is_sat

    @staticmethod
    @pytest.mark.parametrize("color_num, edges, is_sat",
                             [(color_num, COLORING_MANY_EDGES, (color_num >= 5)) for color_num in range(1, 7)])
    def test_coloring_many_edges(color_num: int, edges, is_sat: bool):
        # When colors are 1 ... 100:
        # Variables:  4600 , clauses:  236646
        # Ran in 17s
        # When colors are 1 ... 500:
        # Variables:  23000 , clauses:  5783046
        # Ran in 9m 31s
        # When colors are 1 ... 750:
        # Variables:  34500 , clauses:  12987046
        # Ran in 39m
        assert SATSolver(TestSATSolver.generate_coloring_clauses(color_num, edges)).solve() is is_sat

    @staticmethod
    @pytest.mark.parametrize("color_num", list(range(1, 8)))
    def test_coloring_clique_uncolorable(color_num: int):
        edges = list(combinations(list(range(1, color_num + 2)), 2))
        formula = TestSATSolver.generate_coloring_clauses(color_num, edges)
        assert not SATSolver(formula, halving_period=10000).solve()

    @staticmethod
    @pytest.mark.parametrize("color_num", list(range(7, 10)))
    def test_coloring_clique_uncolorable_2(color_num: int):
        edges = list(combinations(list(range(1, color_num + 2)), 2))
        formula = TestSATSolver.generate_coloring_clauses(color_num, edges)
        assert not SATSolver(formula, halving_period=10000).solve()

    @staticmethod
    @pytest.mark.parametrize("color_num", list(range(1, 21)))
    def test_coloring_clique_colorable(color_num: int):
        edges = list(combinations(list(range(1, color_num + 1)), 2))
        formula = TestSATSolver.generate_coloring_clauses(color_num, edges)
        assert SATSolver(formula, halving_period=float('inf')).solve()

    @staticmethod
    def test_does_not_work():
        color_num = 21
        edges = list(combinations(list(range(1, color_num + 1)), 2))
        formula = TestSATSolver.generate_coloring_clauses(color_num, edges)
        assert SATSolver(formula, halving_period=1000).solve()

    @staticmethod
    @pytest.mark.parametrize("variable_num, clause_num, clause_length",
                             [(200, clause_num, 3) for clause_num in list(range(40000, 61000))])
    def test_random_cnf(variable_num: int, clause_num: int, clause_length: int):
        # Generates a random CNF and compares our solver to Z3

        # Generate formula
        formula_z3 = []
        formula_our = set()

        all_variables_z3 = numpy.array([(z3.Bool(str(cur_literal)), z3.Not(z3.Bool(str(cur_literal)))) for cur_literal
                                        in range(1, variable_num + 1)]).flatten()
        all_variables_our = numpy.array([(variable, -variable) for variable in range(1, variable_num + 1)]).flatten()

        for cur_clause_idx in range(clause_num):
            chosen_literals = numpy.random.randint(0, len(all_variables_our), size=clause_length)
            formula_z3.append(z3.Or(*all_variables_z3[chosen_literals]))
            formula_our.add(frozenset(all_variables_our[chosen_literals]))

        # Solve with Z3
        z3_solver = z3.Solver()
        z3_solver.add(z3.And(*formula_z3))
        start_time_z3 = time.time()
        is_sat_z3 = (z3_solver.check() == z3.sat)
        end_time_z3 = time.time()

        # Solve with our
        start_time_our = time.time()
        our_solver = SATSolver(formula_our)
        is_sat_our = our_solver.solve()
        end_time_our = time.time()

        print()
        print("Is sat? ", is_sat_z3)
        print("Z3:\t\t", end_time_z3 - start_time_z3)
        print("Our:\t", end_time_our - start_time_our)
        assert is_sat_our is is_sat_z3

    @staticmethod
    @pytest.mark.parametrize("variable_num, operator_num, test_parser",
                             [(variable_num, 500 * variable_num, True) for variable_num in list(range(1000, 2000))]
                             # +
                             # [(variable_num, variable_num, False) for variable_num in list(range(1, 5000))]
                             )
    def test_random_formula(variable_num: int, operator_num: int, test_parser):
        # Generates a random formula and compares our solver to Z3

        # Generate formula
        formula_z3 = None
        formula_our_text = None
        # formula_our = None

        all_variables = list(range(1, variable_num + 1))
        all_subformulas_z3 = [z3.Bool(str(cur_literal)) for cur_literal in all_variables]
        all_subformulas_z3.extend([z3.Not(cur_literal) for cur_literal in all_subformulas_z3])
        all_subformulas_our_text = [str(cur_literal) for cur_literal in all_variables]
        all_subformulas_our_text.extend([("not " + cur_literal) for cur_literal in all_subformulas_our_text])
        # all_subformulas_our = [str(cur_literal) for cur_literal in all_variables]
        # all_subformulas_our.extend([("not", cur_literal) for cur_literal in all_subformulas_our])

        for cur_operator_idx in range(operator_num):
            cur_subformula_z3 = None
            cur_subformula_our_text = None
            cur_subformula_our = None
            random_operator = random.randint(1, 5)

            first_parameter_idx = random.randint(1, len(all_subformulas_z3)) - 1
            first_parameter_z3 = all_subformulas_z3[first_parameter_idx]
            first_parameter_our_text = all_subformulas_our_text[first_parameter_idx]
            # first_parameter_our = all_subformulas_our[first_parameter_idx]
            if random_operator == 1:
                cur_subformula_z3 = z3.Not(first_parameter_z3)
                cur_subformula_our_text = "not (" + first_parameter_our_text + ")"
                # cur_subformula_our = "not", first_parameter_our
            else:
                # Boolean operators
                second_parameter_idx = random.randint(1, len(all_subformulas_z3)) - 1
                second_parameter_z3 = all_subformulas_z3[second_parameter_idx]
                second_parameter_our_text = all_subformulas_our_text[second_parameter_idx]
                # second_parameter_our = all_subformulas_our[second_parameter_idx]
                if random_operator == 2:
                    cur_subformula_z3 = z3.And(first_parameter_z3, second_parameter_z3)
                    cur_subformula_our_text = "and (" + first_parameter_our_text + ") (" + second_parameter_our_text \
                                              + ")"
                    # cur_subformula_our = "and", first_parameter_our, second_parameter_our
                elif random_operator == 3:
                    cur_subformula_z3 = z3.Or(first_parameter_z3, second_parameter_z3)
                    cur_subformula_our_text = "or (" + first_parameter_our_text + ") (" + second_parameter_our_text \
                                              + ")"
                    # cur_subformula_our = "or", first_parameter_our, second_parameter_our
                elif random_operator == 4:
                    cur_subformula_z3 = z3.Implies(first_parameter_z3, second_parameter_z3)
                    cur_subformula_our_text = "=> (" + first_parameter_our_text + ") (" + second_parameter_our_text \
                                              + ")"
                    # cur_subformula_our = "=>", first_parameter_our, second_parameter_our
                elif random_operator == 5:
                    cur_subformula_z3 = (first_parameter_z3 == second_parameter_z3)
                    cur_subformula_our_text = "<=> (" + first_parameter_our_text + ") (" + second_parameter_our_text \
                                              + ")"
                    # cur_subformula_our = "<=>", first_parameter_our, second_parameter_our
            all_subformulas_z3.append(cur_subformula_z3)
            all_subformulas_our_text.append(cur_subformula_our_text)
            # all_subformulas_our.append(cur_subformula_our)
            # if formula_z3 is None:
            #     formula_z3 = cur_subformula_z3
            #     formula_our_text = cur_subformula_our_text
            #     formula_our = cur_subformula_our
            # else:
            #     # This is probably UNSAT:
            #     # formula_z3 = z3.And(formula_z3, cur_subformula_z3)
            #     # formula_our_text = "and (" + formula_our_text + ") (" + cur_subformula_our_text + ")"
            #     # formula_our = "and", formula_our, cur_subformula_our
        # This is completely random:
        formula_z3 = cur_subformula_z3
        formula_our_text = cur_subformula_our_text
        # formula_our = cur_subformula_our

        # Solve with Z3
        z3_solver = z3.Solver()
        z3_solver.add(formula_z3)
        start_time_z3 = time.time()
        is_sat_z3 = (z3_solver.check() == z3.sat)
        end_time_z3 = time.time()

        # Solve with ours
        if test_parser:
            formula_our = SATSolver.convert_string_formula(formula_our_text)
        # else:
            # formula_our = SATSolver._tseitin_transform(formula_our)
        start_time_our = time.time()
        our_solver = SATSolver(formula_our)
        is_sat_our = our_solver.solve()
        end_time_our = time.time()

        print()
        print("Is sat? ", is_sat_z3)
        print("Z3:\t\t", end_time_z3 - start_time_z3)
        print("Our:\t", end_time_our - start_time_our)
        print("Z3 formula: ", formula_z3)
        assert is_sat_our is is_sat_z3
