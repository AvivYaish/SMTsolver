import pytest
from sat_solver.sat_solver import SATSolver
from itertools import combinations
from scipy.special import comb
import z3
import random
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

    # @staticmethod
    # @pytest.mark.parametrize("color_num", list(range(21, 22)))
    # def test_coloring_clique_colorable(color_num: int):
    #     edges = list(combinations(list(range(1, color_num + 1)), 2))
    #     formula = TestSATSolver.generate_coloring_clauses(color_num, edges)
    #     assert SATSolver(formula, halving_period=float('inf')).solve()

    @staticmethod
    def test_does_not_work():
        """
        FAILED [  6%]Is sat?  True
Z3:		 0.03494668006896973
Our:	 0.0009925365447998047
Z3 formula:  Or(Or(Or(2 == Not(2), 2 == 2), 1 == Not(1)),
   Implies(Not(2), 2))
Text formula:  or (or (or (<=> (2) (not 2)) (<=> (2) (2))) (<=> (1) (not 1))) (=> (not 2) (2))
Text formula, parsed:  ('or', ('or', ('or', ('<=>', '2', ('not', '2')), ('<=>', '2', '2')), ('<=>', '1', ('not', '1'))), ('=>', ('not', '2'), '2'))
Tseitin:  ({('or', ('or', ('or', ('<=>', '2', ('not', '2')), ('<=>', '2', '2')), ('<=>', '1', ('not', '1'))), ('=>', ('not', '2'), '2')): 1, ('or', ('or', ('<=>', '2', ('not', '2')), ('<=>', '2', '2')), ('<=>', '1', ('not', '1'))): 2, ('=>', ('not', '2'), '2'): 3, ('not', '2'): 4, '2': 5, ('or', ('<=>', '2', ('not', '2')), ('<=>', '2', '2')): 6, ('<=>', '1', ('not', '1')): 7, '1': 8, ('not', '1'): 9, ('<=>', '2', ('not', '2')): 10, ('<=>', '2', '2'): 11}, {1: {frozenset({2, 3, -1}), frozenset({1, -3}), frozenset({1, -2})}, 3: {frozenset({3, 4}), frozenset({3, -5}), frozenset({5, -4, -3})}, 4: {frozenset({-5, -4}), frozenset({4, 5})}, 2: {frozenset({-6, 2}), frozenset({-7, 2}), frozenset({7, -2, 6})}, 7: {frozenset({8, -7, -9}), frozenset({-8, -7, 9}), frozenset({-8, -9, 7}), frozenset({8, 9, 7})}, 9: {frozenset({8, 9}), frozenset({-8, -9})}, 6: {frozenset({11, -6, 10}), frozenset({-10, 6}), frozenset({-11, 6})}, 11: {frozenset({11, 5}), frozenset({11, -5}), frozenset({5, -5, -11})}, 10: {frozenset({-4, 5, -10}), frozenset({10, -5, -4}), frozenset({-5, 4, -10}), frozenset({10, 4, 5})}}, {frozenset({5, -4, -3}), frozenset({1, -3}), frozenset({7, -2, 6}), frozenset({-10, 6}), frozenset({-4, 5, -10}), frozenset({5, -5, -11}), frozenset({4, 5}), frozenset({3, -5}), frozenset({2, 3, -1}), frozenset({8, -7, -9}), frozenset({-8, -7, 9}), frozenset({11, -6, 10}), frozenset({1}), frozenset({10, 4, 5}), frozenset({-8, -9, 7}), frozenset({-5, 4, -10}), frozenset({-11, 6}), frozenset({3, 4}), frozenset({-6, 2}), frozenset({-7, 2}), frozenset({11, 5}), frozenset({1, -2}), frozenset({8, 9}), frozenset({-5, -4}), frozenset({-8, -9}), frozenset({11, -5}), frozenset({8, 9, 7}), frozenset({10, -5, -4})})
Our formula:  {frozenset({5, -4, -3}), frozenset({1, -3}), frozenset({7, -2, 6}), frozenset({-10, 6}), frozenset({-4, 5, -10}), frozenset({5, -5, -11}), frozenset({4, 5}), frozenset({3, -5}), frozenset({2, 3, -1}), frozenset({8, -7, -9}), frozenset({-8, -7, 9}), frozenset({11, -6, 10}), frozenset({1}), frozenset({10, 4, 5}), frozenset({-8, -9, 7}), frozenset({-5, 4, -10}), frozenset({-11, 6}), frozenset({3, 4}), frozenset({-6, 2}), frozenset({-7, 2}), frozenset({11, 5}), frozenset({1, -2}), frozenset({8, 9}), frozenset({-5, -4}), frozenset({-8, -9}), frozenset({11, -5}), frozenset({8, 9, 7}), frozenset({10, -5, -4})}
SAT
Z3:  []
        """
        formula1 = "or (or ( or ( <= > (2)(not 2)) (<= > (2)(2))) (<= > (1)(not 1))) (= > ( not 2)(2))" # SAT, []

        """
        FAILED [ 12%]Is sat?  True
Z3:		 0.05485796928405762
Our:	 0.0
Z3 formula:  Or(Or(Or(Not(1) == 1, Or(2, Not(1) == 1)),
      Or(2, Not(1) == 1) == Or(2, Not(1) == 1)),
   Implies(2, Or(2, Not(1) == 1) == Or(2, Not(1) == 1)))
Text formula:  or (or (or (<=> (not 1) (1)) (or (2) (<=> (not 1) (1)))) (<=> (or (2) (<=> (not 1) (1))) (or (2) (<=> (not 1) (1))))) (=> (2) (<=> (or (2) (<=> (not 1) (1))) (or (2) (<=> (not 1) (1)))))
Text formula, parsed:  ('or', ('or', ('or', ('<=>', ('not', '1'), '1'), ('or', '2', ('<=>', ('not', '1'), '1'))), ('<=>', ('or', '2', ('<=>', ('not', '1'), '1')), ('or', '2', ('<=>', ('not', '1'), '1')))), ('=>', '2', ('<=>', ('or', '2', ('<=>', ('not', '1'), '1')), ('or', '2', ('<=>', ('not', '1'), '1')))))
Tseitin:  ({('or', ('or', ('or', ('<=>', ('not', '1'), '1'), ('or', '2', ('<=>', ('not', '1'), '1'))), ('<=>', ('or', '2', ('<=>', ('not', '1'), '1')), ('or', '2', ('<=>', ('not', '1'), '1')))), ('=>', '2', ('<=>', ('or', '2', ('<=>', ('not', '1'), '1')), ('or', '2', ('<=>', ('not', '1'), '1'))))): 1, ('or', ('or', ('<=>', ('not', '1'), '1'), ('or', '2', ('<=>', ('not', '1'), '1'))), ('<=>', ('or', '2', ('<=>', ('not', '1'), '1')), ('or', '2', ('<=>', ('not', '1'), '1')))): 2, ('=>', '2', ('<=>', ('or', '2', ('<=>', ('not', '1'), '1')), ('or', '2', ('<=>', ('not', '1'), '1')))): 3, '2': 4, ('<=>', ('or', '2', ('<=>', ('not', '1'), '1')), ('or', '2', ('<=>', ('not', '1'), '1'))): 5, ('or', '2', ('<=>', ('not', '1'), '1')): 6, ('<=>', ('not', '1'), '1'): 7, ('not', '1'): 8, '1': 9, ('or', ('<=>', ('not', '1'), '1'), ('or', '2', ('<=>', ('not', '1'), '1'))): 10}, {1: {frozenset({2, 3, -1}), frozenset({1, -3}), frozenset({1, -2})}, 3: {frozenset({3, 4}), frozenset({3, -5}), frozenset({5, -4, -3})}, 5: {frozenset({-6, 5}), frozenset({5, 6}), frozenset({-6, -5, 6})}, 6: {frozenset({-6, 4, 7}), frozenset({-7, 6}), frozenset({-4, 6})}, 7: {frozenset({8, -7, -9}), frozenset({-8, -7, 9}), frozenset({-8, -9, 7}), frozenset({8, 9, 7})}, 8: {frozenset({8, 9}), frozenset({-8, -9})}, 2: {frozenset({10, 5, -2}), frozenset({2, -10}), frozenset({2, -5})}, 10: {frozenset({-6, 10}), frozenset({6, -10, 7}), frozenset({-7, 10})}}, {frozenset({5, -4, -3}), frozenset({1, -3}), frozenset({-6, 4, 7}), frozenset({3, -5}), frozenset({2, 3, -1}), frozenset({8, -7, -9}), frozenset({2, -10}), frozenset({6, -10, 7}), frozenset({10, 5, -2}), frozenset({-8, -7, 9}), frozenset({-6, 10}), frozenset({1}), frozenset({-6, 5}), frozenset({2, -5}), frozenset({-8, -9, 7}), frozenset({-7, 6}), frozenset({-7, 10}), frozenset({3, 4}), frozenset({1, -2}), frozenset({8, 9}), frozenset({-4, 6}), frozenset({-8, -9}), frozenset({5, 6}), frozenset({-6, -5, 6}), frozenset({8, 9, 7})})
Our formula:  {frozenset({5, -4, -3}), frozenset({1, -3}), frozenset({-6, 4, 7}), frozenset({3, -5}), frozenset({2, 3, -1}), frozenset({8, -7, -9}), frozenset({2, -10}), frozenset({6, -10, 7}), frozenset({10, 5, -2}), frozenset({-8, -7, 9}), frozenset({-6, 10}), frozenset({1}), frozenset({-6, 5}), frozenset({2, -5}), frozenset({-8, -9, 7}), frozenset({-7, 6}), frozenset({-7, 10}), frozenset({3, 4}), frozenset({1, -2}), frozenset({8, 9}), frozenset({-4, 6}), frozenset({-8, -9}), frozenset({5, 6}), frozenset({-6, -5, 6}), frozenset({8, 9, 7})}
SAT
Z3:  []
        """
        formula2 = "or (or (or (<=> (not 1) (1)) (or (2) (<=> (not 1) (1)))) (<=> (or (2) (<=> (not 1) (1))) (or (2) (<=> (not 1) (1))))) (=> (2) (<=> (or (2) (<=> (not 1) (1))) (or (2) (<=> (not 1) (1)))))" # SAT, []

        """
        FAILED [ 37%]Is sat?  True
Z3:		 0.017919301986694336
Our:	 0.0
Z3 formula:  Or(Or(Or(Not(Not(2)), 1 == Not(1)), Not(Not(2))),
   Or(Not(1), 1 == Not(1)))
Text formula:  or (or (or (not (not 2)) (<=> (1) (not 1))) (not (not 2))) (or (not 1) (<=> (1) (not 1)))
Text formula, parsed:  ('or', ('or', ('or', ('not', ('not', '2')), ('<=>', '1', ('not', '1'))), ('not', ('not', '2'))), ('or', ('not', '1'), ('<=>', '1', ('not', '1'))))
Tseitin:  ({('or', ('or', ('or', ('not', ('not', '2')), ('<=>', '1', ('not', '1'))), ('not', ('not', '2'))), ('or', ('not', '1'), ('<=>', '1', ('not', '1')))): 1, ('or', ('or', ('not', ('not', '2')), ('<=>', '1', ('not', '1'))), ('not', ('not', '2'))): 2, ('or', ('not', '1'), ('<=>', '1', ('not', '1'))): 3, ('not', '1'): 4, ('<=>', '1', ('not', '1')): 5, '1': 6, ('or', ('not', ('not', '2')), ('<=>', '1', ('not', '1'))): 7, ('not', ('not', '2')): 8, ('not', '2'): 9, '2': 10}, {1: {frozenset({2, 3, -1}), frozenset({1, -3}), frozenset({1, -2})}, 3: {frozenset({3, -5}), frozenset({3, -4}), frozenset({5, 4, -3})}, 5: {frozenset({-5, -4, 6}), frozenset({4, 5, 6}), frozenset({-6, -5, 4}), frozenset({-6, -4, 5})}, 4: {frozenset({-6, -4}), frozenset({4, 6})}, 2: {frozenset({-8, 2}), frozenset({-7, 2}), frozenset({8, -2, 7})}, 8: {frozenset({8, 9}), frozenset({-8, -9})}, 9: {frozenset({9, 10}), frozenset({-10, -9})}, 7: {frozenset({8, -7, 5}), frozenset({-8, 7}), frozenset({-5, 7})}}, {frozenset({-8, 2}), frozenset({8, -7, 5}), frozenset({5, 4, -3}), frozenset({1, -3}), frozenset({4, 6}), frozenset({-8, 7}), frozenset({3, -5}), frozenset({2, 3, -1}), frozenset({-6, -4}), frozenset({-5, 7}), frozenset({1}), frozenset({4, 5, 6}), frozenset({-5, -4, 6}), frozenset({-7, 2}), frozenset({1, -2}), frozenset({9, 10}), frozenset({-10, -9}), frozenset({8, 9}), frozenset({-6, -5, 4}), frozenset({3, -4}), frozenset({-8, -9}), frozenset({-6, -4, 5}), frozenset({8, -2, 7})})
Our formula:  {frozenset({-8, 2}), frozenset({8, -7, 5}), frozenset({5, 4, -3}), frozenset({1, -3}), frozenset({4, 6}), frozenset({-8, 7}), frozenset({3, -5}), frozenset({2, 3, -1}), frozenset({-6, -4}), frozenset({-5, 7}), frozenset({1}), frozenset({4, 5, 6}), frozenset({-5, -4, 6}), frozenset({-7, 2}), frozenset({1, -2}), frozenset({9, 10}), frozenset({-10, -9}), frozenset({8, 9}), frozenset({-6, -5, 4}), frozenset({3, -4}), frozenset({-8, -9}), frozenset({-6, -4, 5}), frozenset({8, -2, 7})}
SAT
Z3:  [2 = False, 1 = False]
        """

        """
        FAILED [ 56%]Is sat?  True
Z3:		 0.014008760452270508
Our:	 0.0
Z3 formula:  Or(Or(Or(1 == Not(1), Not(1 == Not(1))), Not(1)),
   Or(Not(1), 1 == Not(1)))
Text formula:  or (or (or (<=> (1) (not 1)) (not (<=> (1) (not 1)))) (not (1))) (or (not (1)) (<=> (1) (not 1)))
Text formula, parsed:  ('or', ('or', ('or', ('<=>', '1', ('not', '1')), ('not', ('<=>', '1', ('not', '1')))), ('not', '1')), ('or', ('not', '1'), ('<=>', '1', ('not', '1'))))
Tseitin:  ({('or', ('or', ('or', ('<=>', '1', ('not', '1')), ('not', ('<=>', '1', ('not', '1')))), ('not', '1')), ('or', ('not', '1'), ('<=>', '1', ('not', '1')))): 1, ('or', ('or', ('<=>', '1', ('not', '1')), ('not', ('<=>', '1', ('not', '1')))), ('not', '1')): 2, ('or', ('not', '1'), ('<=>', '1', ('not', '1'))): 3, ('not', '1'): 4, ('<=>', '1', ('not', '1')): 5, '1': 6, ('or', ('<=>', '1', ('not', '1')), ('not', ('<=>', '1', ('not', '1')))): 7, ('not', ('<=>', '1', ('not', '1'))): 8}, {1: {frozenset({2, 3, -1}), frozenset({1, -3}), frozenset({1, -2})}, 3: {frozenset({3, -5}), frozenset({3, -4}), frozenset({5, 4, -3})}, 5: {frozenset({-5, -4, 6}), frozenset({4, 5, 6}), frozenset({-6, -5, 4}), frozenset({-6, -4, 5})}, 4: {frozenset({-6, -4}), frozenset({4, 6})}, 2: {frozenset({-7, 2}), frozenset({2, -4}), frozenset({4, -2, 7})}, 7: {frozenset({8, -7, 5}), frozenset({-5, 7}), frozenset({-8, 7})}, 8: {frozenset({8, 5}), frozenset({-8, -5})}}, {frozenset({8, -7, 5}), frozenset({-8, 7}), frozenset({1, -3}), frozenset({4, 6}), frozenset({3, -5}), frozenset({2, 3, -1}), frozenset({-6, -4}), frozenset({-5, 7}), frozenset({4, -2, 7}), frozenset({1}), frozenset({4, 5, 6}), frozenset({-5, -4, 6}), frozenset({-7, 2}), frozenset({1, -2}), frozenset({-8, -5}), frozenset({-6, -5, 4}), frozenset({3, -4}), frozenset({-6, -4, 5}), frozenset({2, -4}), frozenset({8, 5}), frozenset({5, 4, -3})})
Our formula:  {frozenset({8, -7, 5}), frozenset({-8, 7}), frozenset({1, -3}), frozenset({4, 6}), frozenset({3, -5}), frozenset({2, 3, -1}), frozenset({-6, -4}), frozenset({-5, 7}), frozenset({4, -2, 7}), frozenset({1}), frozenset({4, 5, 6}), frozenset({-5, -4, 6}), frozenset({-7, 2}), frozenset({1, -2}), frozenset({-8, -5}), frozenset({-6, -5, 4}), frozenset({3, -4}), frozenset({-6, -4, 5}), frozenset({2, -4}), frozenset({8, 5}), frozenset({5, 4, -3})}
SAT
Z3:  []
        """

        """
        FAILED [ 27%]Is sat?  True
Z3:		 0.0329127311706543
Our:	 0.0009975433349609375
Z3 formula:  Or(Or(Or(Not(2) == 2, Implies(Not(2), Not(1))),
      Implies(Implies(Not(2), Not(1)), Not(1))),
   And(Not(2) == 2, Implies(Not(2), Not(1))))
Text formula:  or (or (or (<=> (not 2) (2)) (=> (not 2) (not 1))) (=> (=> (not 2) (not 1)) (not 1))) (and (<=> (not 2) (2)) (=> (not 2) (not 1)))
Text formula, parsed:  ('or', ('or', ('or', ('<=>', ('not', '2'), '2'), ('=>', ('not', '2'), ('not', '1'))), ('=>', ('=>', ('not', '2'), ('not', '1')), ('not', '1'))), ('and', ('<=>', ('not', '2'), '2'), ('=>', ('not', '2'), ('not', '1'))))
Tseitin:  ({('or', ('or', ('or', ('<=>', ('not', '2'), '2'), ('=>', ('not', '2'), ('not', '1'))), ('=>', ('=>', ('not', '2'), ('not', '1')), ('not', '1'))), ('and', ('<=>', ('not', '2'), '2'), ('=>', ('not', '2'), ('not', '1')))): 1, ('or', ('or', ('<=>', ('not', '2'), '2'), ('=>', ('not', '2'), ('not', '1'))), ('=>', ('=>', ('not', '2'), ('not', '1')), ('not', '1'))): 2, ('and', ('<=>', ('not', '2'), '2'), ('=>', ('not', '2'), ('not', '1'))): 3, ('<=>', ('not', '2'), '2'): 4, ('=>', ('not', '2'), ('not', '1')): 5, ('not', '2'): 6, ('not', '1'): 7, '1': 8, '2': 9, ('or', ('<=>', ('not', '2'), '2'), ('=>', ('not', '2'), ('not', '1'))): 10, ('=>', ('=>', ('not', '2'), ('not', '1')), ('not', '1')): 11}, {1: {frozenset({2, 3, -1}), frozenset({1, -3}), frozenset({1, -2})}, 3: {frozenset({4, -3}), frozenset({5, -3}), frozenset({3, -5, -4})}, 5: {frozenset({-6, -5, 7}), frozenset({5, 6}), frozenset({-7, 5})}, 7: {frozenset({-8, -7}), frozenset({8, 7})}, 6: {frozenset({-6, -9}), frozenset({9, 6})}, 4: {frozenset({9, 4, 6}), frozenset({9, -6, -4}), frozenset({-4, 6, -9}), frozenset({-6, 4, -9})}, 2: {frozenset({2, -11}), frozenset({2, -10}), frozenset({10, 11, -2})}, 11: {frozenset({-5, -11, 7}), frozenset({11, 5}), frozenset({-7, 11})}, 10: {frozenset({4, 5, -10}), frozenset({10, -5}), frozenset({10, -4})}}, {frozenset({1, -3}), frozenset({9, -6, -4}), frozenset({4, 5, -10}), frozenset({2, 3, -1}), frozenset({9, 4, 6}), frozenset({2, -10}), frozenset({10, 11, -2}), frozenset({10, -4}), frozenset({8, 7}), frozenset({-6, -9}), frozenset({1}), frozenset({-4, 6, -9}), frozenset({-7, 5}), frozenset({3, -5, -4}), frozenset({-6, -5, 7}), frozenset({9, 6}), frozenset({11, 5}), frozenset({1, -2}), frozenset({10, -5}), frozenset({-7, 11}), frozenset({2, -11}), frozenset({-5, -11, 7}), frozenset({5, 6}), frozenset({-6, 4, -9}), frozenset({4, -3}), frozenset({-8, -7}), frozenset({5, -3})})
Our formula:  {frozenset({1, -3}), frozenset({9, -6, -4}), frozenset({4, 5, -10}), frozenset({2, 3, -1}), frozenset({9, 4, 6}), frozenset({2, -10}), frozenset({10, 11, -2}), frozenset({10, -4}), frozenset({8, 7}), frozenset({-6, -9}), frozenset({1}), frozenset({-4, 6, -9}), frozenset({-7, 5}), frozenset({3, -5, -4}), frozenset({-6, -5, 7}), frozenset({9, 6}), frozenset({11, 5}), frozenset({1, -2}), frozenset({10, -5}), frozenset({-7, 11}), frozenset({2, -11}), frozenset({-5, -11, 7}), frozenset({5, 6}), frozenset({-6, 4, -9}), frozenset({4, -3}), frozenset({-8, -7}), frozenset({5, -3})}
SAT
Z3:  []
        """

        """
        FAILED [ 32%]Is sat?  True
Z3:		 0.041924476623535156
Our:	 0.0
Z3 formula:  Or(Or(Or(And(Not(1), Not(2)), 1 == Not(1)),
      And(Not(1), Not(2)) == 1),
   Not(2) == (1 == Not(1)))
Text formula:  or (or (or (and (not 1) (not 2)) (<=> (1) (not 1))) (<=> (and (not 1) (not 2)) (1))) (<=> (not 2) (<=> (1) (not 1)))
Text formula, parsed:  ('or', ('or', ('or', ('and', ('not', '1'), ('not', '2')), ('<=>', '1', ('not', '1'))), ('<=>', ('and', ('not', '1'), ('not', '2')), '1')), ('<=>', ('not', '2'), ('<=>', '1', ('not', '1'))))
Tseitin:  ({('or', ('or', ('or', ('and', ('not', '1'), ('not', '2')), ('<=>', '1', ('not', '1'))), ('<=>', ('and', ('not', '1'), ('not', '2')), '1')), ('<=>', ('not', '2'), ('<=>', '1', ('not', '1')))): 1, ('or', ('or', ('and', ('not', '1'), ('not', '2')), ('<=>', '1', ('not', '1'))), ('<=>', ('and', ('not', '1'), ('not', '2')), '1')): 2, ('<=>', ('not', '2'), ('<=>', '1', ('not', '1'))): 3, ('not', '2'): 4, ('<=>', '1', ('not', '1')): 5, '1': 6, ('not', '1'): 7, '2': 8, ('or', ('and', ('not', '1'), ('not', '2')), ('<=>', '1', ('not', '1'))): 9, ('<=>', ('and', ('not', '1'), ('not', '2')), '1'): 10, ('and', ('not', '1'), ('not', '2')): 11}, {1: {frozenset({2, 3, -1}), frozenset({1, -3}), frozenset({1, -2})}, 3: {frozenset({5, -4, -3}), frozenset({-5, 4, -3}), frozenset({3, -4, -5}), frozenset({3, 4, 5})}, 5: {frozenset({-7, -6, 5}), frozenset({-6, -5, 7}), frozenset({5, 6, 7}), frozenset({-7, -5, 6})}, 7: {frozenset({6, 7}), frozenset({-7, -6})}, 4: {frozenset({-8, -4}), frozenset({8, 4})}, 2: {frozenset({9, 10, -2}), frozenset({2, -10}), frozenset({2, -9})}, 10: {frozenset({10, -6, -11}), frozenset({-6, 11, -10}), frozenset({-11, -10, 6}), frozenset({10, 11, 6})}, 11: {frozenset({-11, 7}), frozenset({4, -11}), frozenset({-7, 11, -4})}, 9: {frozenset({9, -11}), frozenset({11, 5, -9}), frozenset({9, -5})}}, {frozenset({9, 10, -2}), frozenset({5, -4, -3}), frozenset({1, -3}), frozenset({-6, 11, -10}), frozenset({-7, 11, -4}), frozenset({2, 3, -1}), frozenset({6, 7}), frozenset({2, -10}), frozenset({-7, -5, 6}), frozenset({1}), frozenset({10, 11, 6}), frozenset({9, -11}), frozenset({3, -4, -5}), frozenset({-11, -10, 6}), frozenset({-7, -6, 5}), frozenset({-6, -5, 7}), frozenset({1, -2}), frozenset({2, -9}), frozenset({-8, -4}), frozenset({-5, 4, -3}), frozenset({10, -6, -11}), frozenset({9, -5}), frozenset({-11, 7}), frozenset({5, 6, 7}), frozenset({4, -11}), frozenset({3, 4, 5}), frozenset({-7, -6}), frozenset({11, 5, -9}), frozenset({8, 4})})
Our formula:  {frozenset({9, 10, -2}), frozenset({5, -4, -3}), frozenset({1, -3}), frozenset({-6, 11, -10}), frozenset({-7, 11, -4}), frozenset({2, 3, -1}), frozenset({6, 7}), frozenset({2, -10}), frozenset({-7, -5, 6}), frozenset({1}), frozenset({10, 11, 6}), frozenset({9, -11}), frozenset({3, -4, -5}), frozenset({-11, -10, 6}), frozenset({-7, -6, 5}), frozenset({-6, -5, 7}), frozenset({1, -2}), frozenset({2, -9}), frozenset({-8, -4}), frozenset({-5, 4, -3}), frozenset({10, -6, -11}), frozenset({9, -5}), frozenset({-11, 7}), frozenset({5, 6, 7}), frozenset({4, -11}), frozenset({3, 4, 5}), frozenset({-7, -6}), frozenset({11, 5, -9}), frozenset({8, 4})}
SAT
Z3:  [2 = False, 1 = False]
        """

        """
        FAILED [ 99%]Is sat?  True
Z3:		 0.031877994537353516
Our:	 0.0009975433349609375
Z3 formula:  Or(Or(Or(2 == Not(2), Not(2 == Not(2))), Or(2, 2)),
   Not(2) == (2 == Not(2)))
Text formula:  or (or (or (<=> (2) (not 2)) (not (<=> (2) (not 2)))) (or (2) (2))) (<=> (not 2) (<=> (2) (not 2)))
Text formula, parsed:  ('or', ('or', ('or', ('<=>', '2', ('not', '2')), ('not', ('<=>', '2', ('not', '2')))), ('or', '2', '2')), ('<=>', ('not', '2'), ('<=>', '2', ('not', '2'))))
Tseitin:  ({('or', ('or', ('or', ('<=>', '2', ('not', '2')), ('not', ('<=>', '2', ('not', '2')))), ('or', '2', '2')), ('<=>', ('not', '2'), ('<=>', '2', ('not', '2')))): 1, ('or', ('or', ('<=>', '2', ('not', '2')), ('not', ('<=>', '2', ('not', '2')))), ('or', '2', '2')): 2, ('<=>', ('not', '2'), ('<=>', '2', ('not', '2'))): 3, ('not', '2'): 4, ('<=>', '2', ('not', '2')): 5, '2': 6, ('or', ('<=>', '2', ('not', '2')), ('not', ('<=>', '2', ('not', '2')))): 7, ('or', '2', '2'): 8, ('not', ('<=>', '2', ('not', '2'))): 9}, {1: {frozenset({2, 3, -1}), frozenset({1, -3}), frozenset({1, -2})}, 3: {frozenset({5, -4, -3}), frozenset({-5, 4, -3}), frozenset({3, -4, -5}), frozenset({3, 4, 5})}, 5: {frozenset({-5, -4, 6}), frozenset({4, 5, 6}), frozenset({-6, -5, 4}), frozenset({-6, -4, 5})}, 4: {frozenset({-6, -4}), frozenset({4, 6})}, 2: {frozenset({-8, 2}), frozenset({-7, 2}), frozenset({8, -2, 7})}, 8: {frozenset({8, -6}), frozenset({-8, 6})}, 7: {frozenset({-5, 7}), frozenset({-7, 5, 9}), frozenset({7, -9})}, 9: {frozenset({-5, -9}), frozenset({9, 5})}}, {frozenset({-8, 2}), frozenset({5, -4, -3}), frozenset({1, -3}), frozenset({4, 6}), frozenset({2, 3, -1}), frozenset({-6, -4}), frozenset({-5, 7}), frozenset({1}), frozenset({4, 5, 6}), frozenset({9, 5}), frozenset({3, -4, -5}), frozenset({-5, -4, 6}), frozenset({-7, 2}), frozenset({1, -2}), frozenset({7, -9}), frozenset({-5, -9}), frozenset({-5, 4, -3}), frozenset({-6, -5, 4}), frozenset({8, -6}), frozenset({-8, 6}), frozenset({-6, -4, 5}), frozenset({-7, 5, 9}), frozenset({3, 4, 5}), frozenset({8, -2, 7})})
Our formula:  {frozenset({8, -7, 5}), frozenset({5, -4, -3}), frozenset({1, -3}), frozenset({4, 6}), frozenset({6, -2, 7}), frozenset({-8, 7}), frozenset({2, 3, -1}), frozenset({-6, -4}), frozenset({-5, 7}), frozenset({1}), frozenset({4, 5, 6}), frozenset({3, -4, -5}), frozenset({-5, -4, 6}), frozenset({-6, 2}), frozenset({-7, 2}), frozenset({1, -2}), frozenset({-8, -5}), frozenset({-5, 4, -3}), frozenset({-6, -5, 4}), frozenset({-6, -4, 5}), frozenset({3, 4, 5}), frozenset({8, 5})}
SAT
Z3:  []
        """

    """
    !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
Is sat?  True
Z3:		 0.016956090927124023
Our:	 0.0009961128234863281
Z3 formula:  Not(And(And(And(Or(And(Or(Not(2), 3),
                       Or(Not(Not(4)), Not(5))) ==
                   Not(Not(Not(1) == 1)),
                   And(Not(3), Not(1))),
                Implies(And(Or(Not(Not(1)) == 2,
                               Or(And(2, Not(1)),
                                  Not(1) == 1)),
                            Not(Or(And(Not(3), Not(1)) ==
                                   (4 == 5),
                                   Not(2)))),
                        Not(1)) ==
                (Or(And(Not(3), Not(1)) == (4 == 5), Not(2)) ==
                 Not(And(Not(3), Not(1)) == (4 == 5)))),
            Not(Implies(And(And(Or(Not(Not(1)) == 2,
                                   Or(And(2, Not(1)),
                                      Not(1) == 1)),
                                Not(Or(And(Not(3), Not(1)) ==
                                       (4 == 5),
                                       Not(2)))),
                            Not(2)),
                        Or(Not(Or(Or(Not(And(Not(3), Not(1)) ==
                                        (4 == 5)),
                                     Not(5)),
                                  Not(Or(And(Not(3), Not(1)) ==
                                        (4 == 5),
                                        Not(2))))),
                           And(Or(And(2, Not(1)),
                                  Not(1) == 1),
                               And(Not(3), Not(1))))))),
        Implies(Implies(And(2, Not(1)), 5),
                Implies(Not(Not(1) == 1) == 4,
                        Or(3 == 5, 2))))) ==
And(Not(Not(Implies(And(2, Not(1)), 5)) ==
        And(Or(Or(Not(Implies(Not(Not(Not(1) == 1) ==
                                  (Not(2) == And(2, Not(1)))),
                              And(Not(Not(1) == 1),
                                  And(Not(3), Not(1))))),
                  Not(3)),
               (Not(2) == (And(Not(3), Not(1)) == (4 == 5))) ==
               (And(And(Not(3), Not(1)), Not(2)) ==
                And(Not(1) == 1,
                    Or(And(Not(3), Not(1)) == (4 == 5),
                       Not(2))))),
            (Not(5) == (Not(1) == 1)) ==
            (Implies(And(Or(Not(Not(1)) == 2,
                            Or(And(2, Not(1)), Not(1) == 1)),
                         Not(Or(And(Not(3), Not(1)) ==
                                (4 == 5),
                                Not(2)))),
                     Not(1)) ==
             (Or(And(Not(3), Not(1)) == (4 == 5), Not(2)) ==
              Not(And(Not(3), Not(1)) == (4 == 5)))))) ==
    Or(And(And(Or(Not(2), 2), And(Not(3), Not(1))),
           (Not(2) == (And(Not(3), Not(1)) == (4 == 5))) ==
           (Not(Not(2) == And(2, Not(1))) == (4 == 5))),
       And(4 == 5,
           (Implies(Implies(And(Or(Not(Not(1)) == 2,
                                   Or(And(2, Not(1)),
                                      Not(1) == 1)),
                                Not(Or(And(Not(3), Not(1)) ==
                                       (4 == 5),
                                       Not(2)))),
                            Not(1)),
                    Not(5)) ==
            Or(1, 4)) ==
           Not((Not(5) == (Not(1) == 1)) ==
               (Implies(And(Or(Not(Not(1)) == 2,
                               Or(And(2, Not(1)),
                                  Not(1) == 1)),
                            Not(Or(And(Not(3), Not(1)) ==
                                   (4 == 5),
                                   Not(2)))),
                        Not(1)) ==
                (Or(And(Not(3), Not(1)) == (4 == 5), Not(2)) ==
                 Not(And(Not(3), Not(1)) == (4 == 5))))))),
    Not(Or(Not(Or(Not(2), 2) ==
               And(Not(1), And(And(Not(3), Not(1)), Not(2)))),
           And(Not(5), Not(4)))))
Z3 formula:  Not(And(And(And(Or(And(Or(Not(2), 3),
                       Or(Not(Not(4)), Not(5))) ==
                   Not(Not(Not(1) == 1)),
                   And(Not(3), Not(1))),
                Implies(And(Or(Not(Not(1)) == 2,
                               Or(And(2, Not(1)),
                                  Not(1) == 1)),
                            Not(Or(And(Not(3), Not(1)) ==
                                   (4 == 5),
                                   Not(2)))),
                        Not(1)) ==
                (Or(And(Not(3), Not(1)) == (4 == 5), Not(2)) ==
                 Not(And(Not(3), Not(1)) == (4 == 5)))),
            Not(Implies(And(And(Or(Not(Not(1)) == 2,
                                   Or(And(2, Not(1)),
                                      Not(1) == 1)),
                                Not(Or(And(Not(3), Not(1)) ==
                                       (4 == 5),
                                       Not(2)))),
                            Not(2)),
                        Or(Not(Or(Or(Not(And(Not(3), Not(1)) ==
                                        (4 == 5)),
                                     Not(5)),
                                  Not(Or(And(Not(3), Not(1)) ==
                                        (4 == 5),
                                        Not(2))))),
                           And(Or(And(2, Not(1)),
                                  Not(1) == 1),
                               And(Not(3), Not(1))))))),
        Implies(Implies(And(2, Not(1)), 5),
                Implies(Not(Not(1) == 1) == 4,
                        Or(3 == 5, 2))))) ==
And(Not(Not(Implies(And(2, Not(1)), 5)) ==
        And(Or(Or(Not(Implies(Not(Not(Not(1) == 1) ==
                                  (Not(2) == And(2, Not(1)))),
                              And(Not(Not(1) == 1),
                                  And(Not(3), Not(1))))),
                  Not(3)),
               (Not(2) == (And(Not(3), Not(1)) == (4 == 5))) ==
               (And(And(Not(3), Not(1)), Not(2)) ==
                And(Not(1) == 1,
                    Or(And(Not(3), Not(1)) == (4 == 5),
                       Not(2))))),
            (Not(5) == (Not(1) == 1)) ==
            (Implies(And(Or(Not(Not(1)) == 2,
                            Or(And(2, Not(1)), Not(1) == 1)),
                         Not(Or(And(Not(3), Not(1)) ==
                                (4 == 5),
                                Not(2)))),
                     Not(1)) ==
             (Or(And(Not(3), Not(1)) == (4 == 5), Not(2)) ==
              Not(And(Not(3), Not(1)) == (4 == 5)))))) ==
    Or(And(And(Or(Not(2), 2), And(Not(3), Not(1))),
           (Not(2) == (And(Not(3), Not(1)) == (4 == 5))) ==
           (Not(Not(2) == And(2, Not(1))) == (4 == 5))),
       And(4 == 5,
           (Implies(Implies(And(Or(Not(Not(1)) == 2,
                                   Or(And(2, Not(1)),
                                      Not(1) == 1)),
                                Not(Or(And(Not(3), Not(1)) ==
                                       (4 == 5),
                                       Not(2)))),
                            Not(1)),
                    Not(5)) ==
            Or(1, 4)) ==
           Not((Not(5) == (Not(1) == 1)) ==
               (Implies(And(Or(Not(Not(1)) == 2,
                               Or(And(2, Not(1)),
                                  Not(1) == 1)),
                            Not(Or(And(Not(3), Not(1)) ==
                                   (4 == 5),
                                   Not(2)))),
                        Not(1)) ==
                (Or(And(Not(3), Not(1)) == (4 == 5), Not(2)) ==
                 Not(And(Not(3), Not(1)) == (4 == 5))))))),
    Not(Or(Not(Or(Not(2), 2) ==
               And(Not(1), And(And(Not(3), Not(1)), Not(2)))),
           And(Not(5), Not(4)))))
Text formula:  <=> (not (and (and (and (or (<=> (and (or (not 2) (3)) (or (not (not 4)) (not (5)))) (not (not (<=> (not 1) (1))))) (and (not 3) (not (1)))) (<=> (=> (and (or (<=> (not (not (1))) (2)) (or (and (2) (not 1)) (<=> (not 1) (1)))) (not (or (<=> (and (not 3) (not (1))) (<=> (4) (5))) (not 2)))) (not (1))) (<=> (or (<=> (and (not 3) (not (1))) (<=> (4) (5))) (not 2)) (not (<=> (and (not 3) (not (1))) (<=> (4) (5))))))) (not (=> (and (and (or (<=> (not (not (1))) (2)) (or (and (2) (not 1)) (<=> (not 1) (1)))) (not (or (<=> (and (not 3) (not (1))) (<=> (4) (5))) (not 2)))) (not (2))) (or (not (or (or (not (<=> (and (not 3) (not (1))) (<=> (4) (5)))) (not (5))) (not (or (<=> (and (not 3) (not (1))) (<=> (4) (5))) (not 2))))) (and (or (and (2) (not 1)) (<=> (not 1) (1))) (and (not 3) (not (1)))))))) (=> (=> (and (2) (not 1)) (5)) (=> (<=> (not (<=> (not 1) (1))) (4)) (or (<=> (3) (5)) (2)))))) (and (<=> (not (<=> (not (=> (and (2) (not 1)) (5))) (and (or (or (not (=> (not (<=> (not (<=> (not 1) (1))) (<=> (not (2)) (and (2) (not 1))))) (and (not (<=> (not 1) (1))) (and (not 3) (not (1)))))) (not 3)) (<=> (<=> (not 2) (<=> (and (not 3) (not (1))) (<=> (4) (5)))) (<=> (and (and (not 3) (not (1))) (not 2)) (and (<=> (not 1) (1)) (or (<=> (and (not 3) (not (1))) (<=> (4) (5))) (not 2)))))) (<=> (<=> (not 5) (<=> (not 1) (1))) (<=> (=> (and (or (<=> (not (not (1))) (2)) (or (and (2) (not 1)) (<=> (not 1) (1)))) (not (or (<=> (and (not 3) (not (1))) (<=> (4) (5))) (not 2)))) (not (1))) (<=> (or (<=> (and (not 3) (not (1))) (<=> (4) (5))) (not 2)) (not (<=> (and (not 3) (not (1))) (<=> (4) (5)))))))))) (or (and (and (or (not (2)) (2)) (and (not 3) (not (1)))) (<=> (<=> (not 2) (<=> (and (not 3) (not (1))) (<=> (4) (5)))) (<=> (not (<=> (not (2)) (and (2) (not 1)))) (<=> (4) (5))))) (and (<=> (4) (5)) (<=> (<=> (=> (=> (and (or (<=> (not (not (1))) (2)) (or (and (2) (not 1)) (<=> (not 1) (1)))) (not (or (<=> (and (not 3) (not (1))) (<=> (4) (5))) (not 2)))) (not (1))) (not 5)) (or (1) (4))) (not (<=> (<=> (not 5) (<=> (not 1) (1))) (<=> (=> (and (or (<=> (not (not (1))) (2)) (or (and (2) (not 1)) (<=> (not 1) (1)))) (not (or (<=> (and (not 3) (not (1))) (<=> (4) (5))) (not 2)))) (not (1))) (<=> (or (<=> (and (not 3) (not (1))) (<=> (4) (5))) (not 2)) (not (<=> (and (not 3) (not (1))) (<=> (4) (5)))))))))))) (not (or (not (<=> (or (not (2)) (2)) (and (not (1)) (and (and (not 3) (not (1))) (not 2))))) (and (not 5) (not (4))))))
Text formula, parsed:  ('<=>', ('not', ('and', ('and', ('and', ('or', ('<=>', ('and', ('or', ('not', '2'), '3'), ('or', ('not', ('not', '4')), ('not', '5'))), ('not', ('not', ('<=>', ('not', '1'), '1')))), ('and', ('not', '3'), ('not', '1'))), ('<=>', ('=>', ('and', ('or', ('<=>', ('not', ('not', '1')), '2'), ('or', ('and', '2', ('not', '1')), ('<=>', ('not', '1'), '1'))), ('not', ('or', ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5')), ('not', '2')))), ('not', '1')), ('<=>', ('or', ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5')), ('not', '2')), ('not', ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5')))))), ('not', ('=>', ('and', ('and', ('or', ('<=>', ('not', ('not', '1')), '2'), ('or', ('and', '2', ('not', '1')), ('<=>', ('not', '1'), '1'))), ('not', ('or', ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5')), ('not', '2')))), ('not', '2')), ('or', ('not', ('or', ('or', ('not', ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5'))), ('not', '5')), ('not', ('or', ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5')), ('not', '2'))))), ('and', ('or', ('and', '2', ('not', '1')), ('<=>', ('not', '1'), '1')), ('and', ('not', '3'), ('not', '1'))))))), ('=>', ('=>', ('and', '2', ('not', '1')), '5'), ('=>', ('<=>', ('not', ('<=>', ('not', '1'), '1')), '4'), ('or', ('<=>', '3', '5'), '2'))))), ('and', ('<=>', ('not', ('<=>', ('not', ('=>', ('and', '2', ('not', '1')), '5')), ('and', ('or', ('or', ('not', ('=>', ('not', ('<=>', ('not', ('<=>', ('not', '1'), '1')), ('<=>', ('not', '2'), ('and', '2', ('not', '1'))))), ('and', ('not', ('<=>', ('not', '1'), '1')), ('and', ('not', '3'), ('not', '1'))))), ('not', '3')), ('<=>', ('<=>', ('not', '2'), ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5'))), ('<=>', ('and', ('and', ('not', '3'), ('not', '1')), ('not', '2')), ('and', ('<=>', ('not', '1'), '1'), ('or', ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5')), ('not', '2')))))), ('<=>', ('<=>', ('not', '5'), ('<=>', ('not', '1'), '1')), ('<=>', ('=>', ('and', ('or', ('<=>', ('not', ('not', '1')), '2'), ('or', ('and', '2', ('not', '1')), ('<=>', ('not', '1'), '1'))), ('not', ('or', ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5')), ('not', '2')))), ('not', '1')), ('<=>', ('or', ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5')), ('not', '2')), ('not', ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5'))))))))), ('or', ('and', ('and', ('or', ('not', '2'), '2'), ('and', ('not', '3'), ('not', '1'))), ('<=>', ('<=>', ('not', '2'), ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5'))), ('<=>', ('not', ('<=>', ('not', '2'), ('and', '2', ('not', '1')))), ('<=>', '4', '5')))), ('and', ('<=>', '4', '5'), ('<=>', ('<=>', ('=>', ('=>', ('and', ('or', ('<=>', ('not', ('not', '1')), '2'), ('or', ('and', '2', ('not', '1')), ('<=>', ('not', '1'), '1'))), ('not', ('or', ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5')), ('not', '2')))), ('not', '1')), ('not', '5')), ('or', '1', '4')), ('not', ('<=>', ('<=>', ('not', '5'), ('<=>', ('not', '1'), '1')), ('<=>', ('=>', ('and', ('or', ('<=>', ('not', ('not', '1')), '2'), ('or', ('and', '2', ('not', '1')), ('<=>', ('not', '1'), '1'))), ('not', ('or', ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5')), ('not', '2')))), ('not', '1')), ('<=>', ('or', ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5')), ('not', '2')), ('not', ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5'))))))))))), ('not', ('or', ('not', ('<=>', ('or', ('not', '2'), '2'), ('and', ('not', '1'), ('and', ('and', ('not', '3'), ('not', '1')), ('not', '2'))))), ('and', ('not', '5'), ('not', '4'))))))
Simplified formula:  ('<=>', ('not', ('and', ('and', ('and', ('or', ('not', ('and', ('or', ('not', '2'), '3'), ('or', '4', ('not', '5')))), ('and', ('not', '3'), ('not', '1'))), ('<=>', ('=>', ('and', ('or', ('<=>', '1', '2'), ('and', '2', ('not', '1'))), ('not', ('or', ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5')), ('not', '2')))), ('not', '1')), ('<=>', ('or', ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5')), ('not', '2')), ('not', ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5')))))), ('not', ('=>', ('and', ('and', ('or', ('<=>', '1', '2'), ('and', '2', ('not', '1'))), ('not', ('or', ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5')), ('not', '2')))), ('not', '2')), ('or', ('not', ('or', ('or', ('not', ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5'))), ('not', '5')), ('not', ('or', ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5')), ('not', '2'))))), ('and', ('and', '2', ('not', '1')), ('and', ('not', '3'), ('not', '1'))))))), ('=>', ('=>', ('and', '2', ('not', '1')), '5'), ('=>', '4', ('or', ('<=>', '3', '5'), '2'))))), ('and', ('<=>', ('not', ('<=>', ('not', ('=>', ('and', '2', ('not', '1')), '5')), ('and', ('or', ('or', ('not', ('=>', ('not', ('<=>', ('not', '2'), ('and', '2', ('not', '1')))), ('and', ('not', '3'), ('not', '1')))), ('not', '3')), ('<=>', ('<=>', ('not', '2'), ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5'))), ('not', ('and', ('and', ('not', '3'), ('not', '1')), ('not', '2'))))), ('<=>', ('not', ('not', '5')), ('<=>', ('=>', ('and', ('or', ('<=>', '1', '2'), ('and', '2', ('not', '1'))), ('not', ('or', ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5')), ('not', '2')))), ('not', '1')), ('<=>', ('or', ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5')), ('not', '2')), ('not', ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5'))))))))), ('or', ('and', ('and', ('not', '3'), ('not', '1')), ('<=>', ('<=>', ('not', '2'), ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5'))), ('<=>', ('not', ('<=>', ('not', '2'), ('and', '2', ('not', '1')))), ('<=>', '4', '5')))), ('and', ('<=>', '4', '5'), ('<=>', ('<=>', ('=>', ('=>', ('and', ('or', ('<=>', '1', '2'), ('and', '2', ('not', '1'))), ('not', ('or', ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5')), ('not', '2')))), ('not', '1')), ('not', '5')), ('or', '1', '4')), ('not', ('<=>', ('not', ('not', '5')), ('<=>', ('=>', ('and', ('or', ('<=>', '1', '2'), ('and', '2', ('not', '1'))), ('not', ('or', ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5')), ('not', '2')))), ('not', '1')), ('<=>', ('or', ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5')), ('not', '2')), ('not', ('<=>', ('and', ('not', '3'), ('not', '1')), ('<=>', '4', '5'))))))))))), ('not', ('or', ('not', ('and', ('not', '1'), ('and', ('and', ('not', '3'), ('not', '1')), ('not', '2')))), ('and', ('not', '5'), ('not', '4'))))))
Tseitin on simplified:  {frozenset({23, -25}), frozenset({-48, -47, 26}), frozenset({-22, -50}), frozenset({3, -1, -2}), frozenset({-24, 16}), frozenset({12, -59, -42}), frozenset({59, 62}), frozenset({74, -36}), frozenset({40, -38}), frozenset({4, 22, 23}), frozenset({-16, 26, -37}), frozenset({67, 68}), frozenset({75, -76}), frozenset({-38, 69, -17}), frozenset({17, -78, 21}), frozenset({-47, -45, 46}), frozenset({56, 15}), frozenset({-62, -61, 60}), frozenset({48, -47, -26}), frozenset({65, 12, 21}), frozenset({-71, -73}), frozenset({26, 11, 12}), frozenset({-28, -43, 44}), frozenset({-62, -59, 63}), frozenset({32, 33, 34}), frozenset({-38, 14, -33}), frozenset({16, -14, -19}), frozenset({9, 12}), frozenset({75, -66}), frozenset({-37, -36}), frozenset({32, -66}), frozenset({-16, 14}), frozenset({59, -12}), frozenset({19, 21}), frozenset({32, 30, 31}), frozenset({17, 18}), frozenset({20, -18, -41}), frozenset({27, -28, -29}), frozenset({-69, 38}), frozenset({-24, 23}), frozenset({33, 38}), frozenset({-56, -46, 55}), frozenset({-30, -53, 52}), frozenset({1, -3, -2}), frozenset({-38, 39}), frozenset({17, -42, -49}), frozenset({34, -36, -35}), frozenset({41, -20, -18}), frozenset({-8, 9}), frozenset({73, -74}), frozenset({17, 37, 46}), frozenset({76, 77}), frozenset({27, 28, 29}), frozenset({72, -70, 71}), frozenset({35, -37}), frozenset({-14, 42, -18}), frozenset({-72, 16}), frozenset({-47, -46, 45}), frozenset({-12, -9}), frozenset({-13, 15}), frozenset({-19, 54}), frozenset({-14, -20}), frozenset({-21, 12, -65}), frozenset({-71, 70}), frozenset({27, -25}), frozenset({-46, -45, 47}), frozenset({-55, 53}), frozenset({16, 26, 37}), frozenset({-16, 15, -17}), frozenset({-48, -49}), frozenset({10, 11}), frozenset({-56, -55, 46}), frozenset({33, -14}), frozenset({66, -61}), frozenset({-29, 28, -27}), frozenset({-16, 72, -42}), frozenset({49, 42, 17}), frozenset({40, 35}), frozenset({-42, 14}), frozenset({64, -65}), frozenset({-22, -4, 23}), frozenset({48, 26, 47}), frozenset({-53, 54, 55}), frozenset({-60, 62}), frozenset({65, -21, -12}), frozenset({-52, 53}), frozenset({-30, -29}), frozenset({50, 51, 52}), frozenset({-79, 11, 9}), frozenset({-40, -35}), frozenset({-20, 44}), frozenset({50, -52, -51}), frozenset({36, 37}), frozenset({-42, 39}), frozenset({-15, -14, 13}), frozenset({-16, 24, -45}), frozenset({42, 59}), frozenset({-77, 78}), frozenset({16, -37, -26}), frozenset({-70, 68}), frozenset({-52, 30}), frozenset({61, -67, -66}), frozenset({33, 43}), frozenset({49, -42, -17}), frozenset({64, -63, -11}), frozenset({-46, 37, -17}), frozenset({-60, -2}), frozenset({26, -25}), frozenset({11, -44, 20}), frozenset({-32, -31, 30}), frozenset({45, 46, 47}), frozenset({-11, -10}), frozenset({50, 22}), frozenset({-79, -78, 77}), frozenset({-21, 78}), frozenset({34, 35, 36}), frozenset({-60, 61}), frozenset({9, -43, -33}), frozenset({64, -18}), frozenset({25, -27, -26}), frozenset({5, -3}), frozenset({16, 76, -75}), frozenset({24, -23, 25}), frozenset({-68, -67}), frozenset({-16, 75}), frozenset({74, -9}), frozenset({16, -15}), frozenset({2, -3, -1}), frozenset({-40, -39, 38}), frozenset({1}), frozenset({20, 14}), frozenset({11, -12, -26}), frozenset({51, -52, -50}), frozenset({-7, 6}), frozenset({-7, -13}), frozenset({17, 37, -35}), frozenset({29, 30}), frozenset({18, -42}), frozenset({17, -46, -37}), frozenset({56, 46, 55}), frozenset({35, -36, -34}), frozenset({-6, -5}), frozenset({-72, 42}), frozenset({-77, 79}), frozenset({-15, 17}), frozenset({4, -3}), frozenset({-32, 33, -34}), frozenset({2, 60}), frozenset({39, -41}), frozenset({-23, -22, 4}), frozenset({32, -31, -30}), frozenset({-48, 16, -58}), frozenset({-13, 14}), frozenset({-16, 37, -26}), frozenset({-39, 42, 41}), frozenset({-18, -17}), frozenset({40, 74, -73}), frozenset({29, -28, -27}), frozenset({-40, 73}), frozenset({-59, -51}), frozenset({43, -28, -44}), frozenset({-32, -30, 31}), frozenset({-37, 46, -17}), frozenset({-48, -26, 47}), frozenset({42, -17, -49}), frozenset({17, -69}), frozenset({59, 51}), frozenset({-32, 34, -33}), frozenset({-64, 65, 18}), frozenset({57, 58}), frozenset({-64, 63}), frozenset({-32, 66, -75}), frozenset({32, -34, -33}), frozenset({-31, -9}), frozenset({67, -61}), frozenset({-11, 79}), frozenset({43, -9}), frozenset({9, 36, -74}), frozenset({48, 49}), frozenset({26, -12, -11}), frozenset({-56, -15}), frozenset({-63, 62}), frozenset({-72, 70}), frozenset({-16, 58}), frozenset({-69, -68, 70}), frozenset({78, -17}), frozenset({3, -5, -4}), frozenset({68, 69}), frozenset({12, -11, -26}), frozenset({-44, 28, -43}), frozenset({-58, -57}), frozenset({-54, 53}), frozenset({-8, 10}), frozenset({5, 6}), frozenset({35, -17}), frozenset({41, 18, 20}), frozenset({8, -6, 7}), frozenset({1, 2, 3}), frozenset({-16, 19}), frozenset({48, 58}), frozenset({36, -35, -34}), frozenset({18, -20, -41}), frozenset({54, -57}), frozenset({79, -9}), frozenset({-21, -19}), frozenset({9, 31}), frozenset({44, -11}), frozenset({11, 63}), frozenset({56, -55, -46}), frozenset({73, 71}), frozenset({13, 7}), frozenset({-12, 21, -65}), frozenset({43, 28, 44}), frozenset({-24, 45}), frozenset({-23, -4, 22}), frozenset({57, -54, 19}), frozenset({-8, 6}), frozenset({52, -51, -50}), frozenset({8, -10, -9}), frozenset({-77, -76})}
Tseitin on parsed:  {frozenset({52, 61, 62}), frozenset({3, -1, -2}), frozenset({43, 44, -41}), frozenset({-23, -21}), frozenset({9, -86, 38}), frozenset({-47, 20, -43}), frozenset({76, -75, -74}), frozenset({25, -26}), frozenset({48, 35}), frozenset({-20, 14}), frozenset({-32, -31}), frozenset({32, 33, 34}), frozenset({64, 65}), frozenset({24, 25, 4}), frozenset({-68, -90}), frozenset({59, -61}), frozenset({91, -19}), frozenset({-64, -65}), frozenset({-69, -68, 55}), frozenset({46, 33, 9}), frozenset({-9, 46, -33}), frozenset({27, -29, -28}), frozenset({-31, -30, 29}), frozenset({48, 49, 30}), frozenset({1, -3, -2}), frozenset({-8, 9}), frozenset({18, -50}), frozenset({88, 89, 90}), frozenset({-88, 87}), frozenset({-88, 90, -89}), frozenset({29, 30, 31}), frozenset({-24, 4, -25}), frozenset({-12, -9}), frozenset({91, -89}), frozenset({89, -92, -91}), frozenset({-62, -52, 61}), frozenset({-16, 15, -17}), frozenset({57, 70}), frozenset({26, 27, -25}), frozenset({-16, -22}), frozenset({42, 37}), frozenset({42, -85, 86}), frozenset({73, -71}), frozenset({-48, 9, -35}), frozenset({80, 81}), frozenset({2, 71}), frozenset({-31, -29, 30}), frozenset({28, -27}), frozenset({-38, 86}), frozenset({-38, -36, 37}), frozenset({74, 75}), frozenset({-15, -14, 13}), frozenset({-87, -34, 78}), frozenset({-39, 19, -52}), frozenset({-50, 14}), frozenset({65, -67}), frozenset({26, -51, -50}), frozenset({-40, 42}), frozenset({-39, 52, -19}), frozenset({-62, 63, -17}), frozenset({50, -26}), frozenset({34, 35, 36}), frozenset({-20, -19}), frozenset({-70, 74, -73}), frozenset({11, 28, 12}), frozenset({-45, 20}), frozenset({17, 62, 63}), frozenset({21, -18}), frozenset({-93, 92}), frozenset({18, -67}), frozenset({2, -3, -1}), frozenset({1}), frozenset({-61, -52, 62}), frozenset({-7, 6}), frozenset({20, -76, 77}), frozenset({40, -42, -41}), frozenset({-55, 45, -19}), frozenset({35, -36, -34}), frozenset({29, -27}), frozenset({-46, -37, 63}), frozenset({-15, 17}), frozenset({12, 77, 23}), frozenset({4, -3}), frozenset({90, 68}), frozenset({-86, 85}), frozenset({51, -26}), frozenset({-37, -36, 38}), frozenset({-80, -79}), frozenset({16, -45}), frozenset({-15, -13, 14}), frozenset({-46, -68}), frozenset({68, -67}), frozenset({19, 20}), frozenset({24, -4, -25}), frozenset({19, -37, 39}), frozenset({-55, 19, -45}), frozenset({68, 69, 55}), frozenset({-88, 89, -90}), frozenset({-54, -28, 53}), frozenset({51, 52, 53}), frozenset({-53, 52, -51}), frozenset({32, -34, -33}), frozenset({-72, 71, -73}), frozenset({-20, 76}), frozenset({-19, 14}), frozenset({68, 46}), frozenset({54, 55}), frozenset({40, -81}), frozenset({-46, 44}), frozenset({17, -62, -63}), frozenset({83, 84, -82}), frozenset({-30, -29, 31}), frozenset({49, -11}), frozenset({-78, 34}), frozenset({3, -5, -4}), frozenset({19, 45, 55}), frozenset({-84, 44}), frozenset({16, -46, -22}), frozenset({-78, 87}), frozenset({-16, -47}), frozenset({-48, 49, -30}), frozenset({-8, 10}), frozenset({8, -6, 7}), frozenset({1, 2, 3}), frozenset({-77, 76}), frozenset({9, -46, -33}), frozenset({33, -46, -9}), frozenset({36, -35, -34}), frozenset({-55, -68, 69}), frozenset({11, 22, -49}), frozenset({17, -19, -18}), frozenset({-40, 16, -35}), frozenset({41, -44}), frozenset({67, -68, -18}), frozenset({19, 52, 39}), frozenset({-24, 25, -4}), frozenset({-64, 60}), frozenset({13, 7}), frozenset({-62, -61, 52}), frozenset({-69, -66}), frozenset({-14, 50, -18}), frozenset({32, -58}), frozenset({-44, 45, 46}), frozenset({19, -81}), frozenset({8, -10, -9}), frozenset({82, -84}), frozenset({43, 20, 47}), frozenset({-16, 18, -21}), frozenset({61, 60, -59}), frozenset({24, 56}), frozenset({-70, -57}), frozenset({19, -91, 23}), frozenset({-93, -10}), frozenset({-24, -56}), frozenset({-18, 87}), frozenset({86, -9}), frozenset({28, 53, 54}), frozenset({-48, 30, -49}), frozenset({48, -9}), frozenset({-21, 60}), frozenset({92, -9}), frozenset({16, 46, 22}), frozenset({9, 12}), frozenset({-39, 28, -18}), frozenset({-16, -20, 45}), frozenset({49, -22}), frozenset({-54, -53, 28}), frozenset({-40, 41}), frozenset({11, -68, -75}), frozenset({34, -36, -35}), frozenset({73, 70}), frozenset({-16, -46, 22}), frozenset({73, -74}), frozenset({21, 23}), frozenset({11, 75, 68}), frozenset({10, 11}), frozenset({16, 47}), frozenset({-32, 58, -59}), frozenset({-11, 68, -75}), frozenset({88, -90, -89}), frozenset({-63, 46}), frozenset({88, -87, 18}), frozenset({16, 22}), frozenset({-39, 18, -28}), frozenset({-16, -22, 46}), frozenset({40, 35}), frozenset({-52, -19, 39}), frozenset({-23, -12, 77}), frozenset({92, -89}), frozenset({18, 28, 39}), frozenset({65, 66}), frozenset({-70, -45, 12}), frozenset({-16, 35}), frozenset({-39, -38}), frozenset({11, -28, -12}), frozenset({59, -60}), frozenset({-55, -69, 68}), frozenset({-77, -12, 23}), frozenset({-11, -10}), frozenset({67, -66, -65}), frozenset({5, -3}), frozenset({-23, -77, 12}), frozenset({-14, -13, 15}), frozenset({16, -15}), frozenset({-80, 82, -81}), frozenset({53, -52, -51}), frozenset({18, -17}), frozenset({-7, -13}), frozenset({75, -68, -11}), frozenset({-6, -5}), frozenset({9, -92, 93}), frozenset({-85, -83}), frozenset({19, -17}), frozenset({-12, 28, -11}), frozenset({-32, 33, -34}), frozenset({-56, 57, -58}), frozenset({-23, 91}), frozenset({38, 39}), frozenset({-72, 79}), frozenset({10, 93}), frozenset({25, -27}), frozenset({56, -58, -57}), frozenset({-14, 19, 20}), frozenset({-45, -19, 55}), frozenset({-12, 70}), frozenset({-55, -54}), frozenset({-56, 58, -57}), frozenset({18, -84}), frozenset({59, -58}), frozenset({-32, 34, -33}), frozenset({-47, 43, -20}), frozenset({66, 69}), frozenset({-44, -18, 84}), frozenset({-37, -42}), frozenset({48, -30, -49}), frozenset({-63, 37}), frozenset({72, -71}), frozenset({51, -52, -53}), frozenset({13, 14, 15}), frozenset({56, 57, 58}), frozenset({74, -76}), frozenset({16, -18}), frozenset({-20, -43, 47}), frozenset({83, 85}), frozenset({-28, -18, 39}), frozenset({-53, -28, 54}), frozenset({-71, -2}), frozenset({37, -19}), frozenset({-63, 62, -17}), frozenset({5, 6}), frozenset({85, -42}), frozenset({64, -60, 21}), frozenset({41, -43}), frozenset({-72, 78}), frozenset({-45, 44}), frozenset({82, -83}), frozenset({36, 37, 38}), frozenset({80, 79}), frozenset({-40, 81, -19}), frozenset({80, -82}), frozenset({12, -28, -11}), frozenset({-38, -37, 36}), frozenset({32, 31}), frozenset({72, -79, -78}), frozenset({-39, 37}), frozenset({45, 70}), frozenset({-8, 6})}
Our formula:  {frozenset({23, -25}), frozenset({-48, -47, 26}), frozenset({-22, -50}), frozenset({3, -1, -2}), frozenset({-24, 16}), frozenset({12, -59, -42}), frozenset({59, 62}), frozenset({74, -36}), frozenset({40, -38}), frozenset({4, 22, 23}), frozenset({-16, 26, -37}), frozenset({67, 68}), frozenset({75, -76}), frozenset({-38, 69, -17}), frozenset({17, -78, 21}), frozenset({-47, -45, 46}), frozenset({56, 15}), frozenset({-62, -61, 60}), frozenset({48, -47, -26}), frozenset({65, 12, 21}), frozenset({-71, -73}), frozenset({26, 11, 12}), frozenset({-28, -43, 44}), frozenset({-62, -59, 63}), frozenset({32, 33, 34}), frozenset({-38, 14, -33}), frozenset({16, -14, -19}), frozenset({9, 12}), frozenset({75, -66}), frozenset({-37, -36}), frozenset({32, -66}), frozenset({-16, 14}), frozenset({59, -12}), frozenset({19, 21}), frozenset({32, 30, 31}), frozenset({17, 18}), frozenset({20, -18, -41}), frozenset({27, -28, -29}), frozenset({-69, 38}), frozenset({-24, 23}), frozenset({33, 38}), frozenset({-56, -46, 55}), frozenset({-30, -53, 52}), frozenset({1, -3, -2}), frozenset({-38, 39}), frozenset({17, -42, -49}), frozenset({34, -36, -35}), frozenset({41, -20, -18}), frozenset({-8, 9}), frozenset({73, -74}), frozenset({17, 37, 46}), frozenset({76, 77}), frozenset({27, 28, 29}), frozenset({72, -70, 71}), frozenset({35, -37}), frozenset({-14, 42, -18}), frozenset({-72, 16}), frozenset({-47, -46, 45}), frozenset({-12, -9}), frozenset({-13, 15}), frozenset({-19, 54}), frozenset({-14, -20}), frozenset({-21, 12, -65}), frozenset({-71, 70}), frozenset({27, -25}), frozenset({-46, -45, 47}), frozenset({-55, 53}), frozenset({16, 26, 37}), frozenset({-16, 15, -17}), frozenset({-48, -49}), frozenset({10, 11}), frozenset({-56, -55, 46}), frozenset({33, -14}), frozenset({66, -61}), frozenset({-29, 28, -27}), frozenset({-16, 72, -42}), frozenset({49, 42, 17}), frozenset({40, 35}), frozenset({-42, 14}), frozenset({64, -65}), frozenset({-22, -4, 23}), frozenset({48, 26, 47}), frozenset({-53, 54, 55}), frozenset({-60, 62}), frozenset({65, -21, -12}), frozenset({-52, 53}), frozenset({-30, -29}), frozenset({50, 51, 52}), frozenset({-79, 11, 9}), frozenset({-40, -35}), frozenset({-20, 44}), frozenset({50, -52, -51}), frozenset({36, 37}), frozenset({-42, 39}), frozenset({-15, -14, 13}), frozenset({-16, 24, -45}), frozenset({42, 59}), frozenset({-77, 78}), frozenset({16, -37, -26}), frozenset({-70, 68}), frozenset({-52, 30}), frozenset({61, -67, -66}), frozenset({33, 43}), frozenset({49, -42, -17}), frozenset({64, -63, -11}), frozenset({-46, 37, -17}), frozenset({-60, -2}), frozenset({26, -25}), frozenset({11, -44, 20}), frozenset({-32, -31, 30}), frozenset({45, 46, 47}), frozenset({-11, -10}), frozenset({50, 22}), frozenset({-79, -78, 77}), frozenset({-21, 78}), frozenset({34, 35, 36}), frozenset({-60, 61}), frozenset({9, -43, -33}), frozenset({64, -18}), frozenset({25, -27, -26}), frozenset({5, -3}), frozenset({16, 76, -75}), frozenset({24, -23, 25}), frozenset({-68, -67}), frozenset({-16, 75}), frozenset({74, -9}), frozenset({16, -15}), frozenset({2, -3, -1}), frozenset({-40, -39, 38}), frozenset({1}), frozenset({20, 14}), frozenset({11, -12, -26}), frozenset({51, -52, -50}), frozenset({-7, 6}), frozenset({-7, -13}), frozenset({17, 37, -35}), frozenset({29, 30}), frozenset({18, -42}), frozenset({17, -46, -37}), frozenset({56, 46, 55}), frozenset({35, -36, -34}), frozenset({-6, -5}), frozenset({-72, 42}), frozenset({-77, 79}), frozenset({-15, 17}), frozenset({4, -3}), frozenset({-32, 33, -34}), frozenset({2, 60}), frozenset({39, -41}), frozenset({-23, -22, 4}), frozenset({32, -31, -30}), frozenset({-48, 16, -58}), frozenset({-13, 14}), frozenset({-16, 37, -26}), frozenset({-39, 42, 41}), frozenset({-18, -17}), frozenset({40, 74, -73}), frozenset({29, -28, -27}), frozenset({-40, 73}), frozenset({-59, -51}), frozenset({43, -28, -44}), frozenset({-32, -30, 31}), frozenset({-37, 46, -17}), frozenset({-48, -26, 47}), frozenset({42, -17, -49}), frozenset({17, -69}), frozenset({59, 51}), frozenset({-32, 34, -33}), frozenset({-64, 65, 18}), frozenset({57, 58}), frozenset({-64, 63}), frozenset({-32, 66, -75}), frozenset({32, -34, -33}), frozenset({-31, -9}), frozenset({67, -61}), frozenset({-11, 79}), frozenset({43, -9}), frozenset({9, 36, -74}), frozenset({48, 49}), frozenset({26, -12, -11}), frozenset({-56, -15}), frozenset({-63, 62}), frozenset({-72, 70}), frozenset({-16, 58}), frozenset({-69, -68, 70}), frozenset({78, -17}), frozenset({3, -5, -4}), frozenset({68, 69}), frozenset({12, -11, -26}), frozenset({-44, 28, -43}), frozenset({-58, -57}), frozenset({-54, 53}), frozenset({-8, 10}), frozenset({5, 6}), frozenset({35, -17}), frozenset({41, 18, 20}), frozenset({8, -6, 7}), frozenset({1, 2, 3}), frozenset({-16, 19}), frozenset({48, 58}), frozenset({36, -35, -34}), frozenset({18, -20, -41}), frozenset({54, -57}), frozenset({79, -9}), frozenset({-21, -19}), frozenset({9, 31}), frozenset({44, -11}), frozenset({11, 63}), frozenset({56, -55, -46}), frozenset({73, 71}), frozenset({13, 7}), frozenset({-12, 21, -65}), frozenset({43, 28, 44}), frozenset({-24, 45}), frozenset({-23, -4, 22}), frozenset({57, -54, 19}), frozenset({-8, 6}), frozenset({52, -51, -50}), frozenset({8, -10, -9}), frozenset({-77, -76})}
SAT
Z3:  [1 = False, 2 = False, 3 = False, 4 = False, 5 = True]
    """

    @staticmethod
    @pytest.mark.parametrize("variable_num, operator_num, test_parser",
                             # [(variable_num, 500 * variable_num, True) for variable_num in list(range(5, 6))] * 1000
                             # +
                             [(variable_num, 3 * variable_num, False) for variable_num in list(range(1, 6))] * 100
                             )
    def test_random_formula(variable_num: int, operator_num: int, test_parser):
        # Generates a random formula and compares our solver to Z3

        # Generate formula
        formula_z3 = None
        formula_our_text = None
        formula_our = None

        all_variables = list(range(1, variable_num + 1))
        all_subformulas_z3 = [z3.Bool(str(cur_literal)) for cur_literal in all_variables]
        all_subformulas_z3.extend([z3.Not(cur_literal) for cur_literal in all_subformulas_z3])
        all_subformulas_our_text = [str(cur_literal) for cur_literal in all_variables]
        all_subformulas_our_text.extend([("not " + cur_literal) for cur_literal in all_subformulas_our_text])
        all_subformulas_our = [str(cur_literal) for cur_literal in all_variables]
        all_subformulas_our.extend([("not", cur_literal) for cur_literal in all_subformulas_our])

        for cur_operator_idx in range(operator_num):
            cur_subformula_z3 = None
            cur_subformula_our_text = None
            cur_subformula_our = None
            random_operator = random.randint(1, 5)

            first_parameter_idx = random.randint(1, len(all_subformulas_z3)) - 1
            first_parameter_z3 = all_subformulas_z3[first_parameter_idx]
            first_parameter_our_text = all_subformulas_our_text[first_parameter_idx]
            first_parameter_our = all_subformulas_our[first_parameter_idx]
            if random_operator == 1:
                cur_subformula_z3 = z3.Not(first_parameter_z3)
                cur_subformula_our_text = "not (" + first_parameter_our_text + ")"
                cur_subformula_our = "not", first_parameter_our
            else:
                # Boolean operators
                second_parameter_idx = random.randint(1, len(all_subformulas_z3)) - 1
                second_parameter_z3 = all_subformulas_z3[second_parameter_idx]
                second_parameter_our_text = all_subformulas_our_text[second_parameter_idx]
                second_parameter_our = all_subformulas_our[second_parameter_idx]
                if random_operator == 2:
                    cur_subformula_z3 = z3.And(first_parameter_z3, second_parameter_z3)
                    cur_subformula_our_text = "and (" + first_parameter_our_text + ") (" + second_parameter_our_text \
                                              + ")"
                    cur_subformula_our = "and", first_parameter_our, second_parameter_our
                # elif random_operator == 3:
                else:
                    cur_subformula_z3 = z3.Or(first_parameter_z3, second_parameter_z3)
                    cur_subformula_our_text = "or (" + first_parameter_our_text + ") (" + second_parameter_our_text \
                                              + ")"
                    cur_subformula_our = "or", first_parameter_our, second_parameter_our
                # elif random_operator == 4:
                #     cur_subformula_z3 = z3.Implies(first_parameter_z3, second_parameter_z3)
                #     cur_subformula_our_text = "=> (" + first_parameter_our_text + ") (" + second_parameter_our_text \
                #                               + ")"
                #     cur_subformula_our = "=>", first_parameter_our, second_parameter_our
                # elif random_operator == 5:
                #     cur_subformula_z3 = (first_parameter_z3 == second_parameter_z3)
                #     cur_subformula_our_text = "<=> (" + first_parameter_our_text + ") (" + second_parameter_our_text \
                #                               + ")"
                #     cur_subformula_our = "<=>", first_parameter_our, second_parameter_our
            all_subformulas_z3.append(cur_subformula_z3)
            all_subformulas_our_text.append(cur_subformula_our_text)
            all_subformulas_our.append(cur_subformula_our)
            if formula_z3 is None:
                formula_z3 = cur_subformula_z3
                formula_our_text = cur_subformula_our_text
                formula_our = cur_subformula_our
            else:
                # formula_z3 = z3.Or(formula_z3, cur_subformula_z3)
                # formula_our_text = "or (" + formula_our_text + ") (" + cur_subformula_our_text + ")"
                # formula_our = "or", formula_our, cur_subformula_our
                formula_z3 = cur_subformula_z3
                formula_our_text = cur_subformula_our_text
                formula_our = cur_subformula_our

        # Solve with Z3
        z3_solver = z3.Solver()
        z3_solver.add(formula_z3)
        start_time_z3 = time.time()
        is_sat_z3 = (z3_solver.check() == z3.sat)
        end_time_z3 = time.time()

        # Solve with ours
        if test_parser:
            formula_our = SATSolver.convert_string_formula(formula_our_text)
        else:
            formula_our = SATSolver._tseitin_transform(formula_our)

        our_solver = SATSolver(formula_our)
        start_time_our = time.time()
        is_sat_our = our_solver.solve()
        end_time_our = time.time()

        if is_sat_our is not is_sat_z3:
            print()
            if end_time_our - start_time_our != 0:
                print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
            print("Is sat? ", is_sat_z3)
            print("Z3:\t\t", end_time_z3 - start_time_z3)
            print("Our:\t", end_time_our - start_time_our)

            print("Z3 formula: ", formula_z3)
            print("Our formula: ", formula_our)
            print("Text formula: ", formula_our_text)
            formula_our_text_parsed = SATSolver._parse_formula(formula_our_text)
            print("Text formula, parsed: ", formula_our_text_parsed)
            print("Tseitin on parsed: ", SATSolver._tseitin_transform(formula_our_text_parsed))
            formula_our_simplified = SATSolver._simplify_formula(formula_our_text_parsed)
            print("Simplified formula: ", formula_our_simplified)
            print("Tseitin on simplified: ", SATSolver._tseitin_transform(formula_our_simplified))
            if is_sat_z3:
                print("SAT")
                print("Z3: ", z3_solver.model())
            else:
                print("UNSAT")
                print(our_solver.get_assignment())
        assert is_sat_our is is_sat_z3
