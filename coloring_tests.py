import unittest
from itertools import combinations
from scipy.special import comb
from sat_solver import SATSolver


class MyTestCase(unittest.TestCase):
    def test_1_color(self):
        colors = [1]
        edges = [
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

        vertices = set()
        for edge in edges:
            v1, v2 = edge
            vertices.add(v1)
            vertices.add(v2)

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

        self.assertEqual(False, SATSolver(all_clauses).solve())

    def test_2_color(self):
        colors = [1, 2]
        edges = [
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

        vertices = set()
        for edge in edges:
            v1, v2 = edge
            vertices.add(v1)
            vertices.add(v2)

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

        self.assertEqual(False, SATSolver(all_clauses).solve())

    def test_3_color(self):
        colors = [1, 2, 3]
        edges = [
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

        vertices = set()
        for edge in edges:
            v1, v2 = edge
            vertices.add(v1)
            vertices.add(v2)

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

        self.assertEqual(False, SATSolver(all_clauses).solve())

    def test_4_color(self):
        colors = [1, 2, 3, 4]
        edges = [
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

        vertices = set()
        for edge in edges:
            v1, v2 = edge
            vertices.add(v1)
            vertices.add(v2)

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

        self.assertEqual(True, SATSolver(all_clauses).solve())

        def test_4_color(self):
            colors = [1, 2, 3, 4]
            edges = [
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

            vertices = set()
            for edge in edges:
                v1, v2 = edge
                vertices.add(v1)
                vertices.add(v2)

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

            self.assertEqual(True, SATSolver(all_clauses).solve())

    def test_5_color(self):
        colors = [1, 2, 3, 4, 5]
        edges = [
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

        vertices = set()
        for edge in edges:
            v1, v2 = edge
            vertices.add(v1)
            vertices.add(v2)

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

        self.assertEqual(True, SATSolver(all_clauses).solve())

    def test_7_color(self):
        colors = [1, 2, 3, 4, 5, 6, 7]
        edges = [
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

        vertices = set()
        for edge in edges:
            v1, v2 = edge
            vertices.add(v1)
            vertices.add(v2)

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

        self.assertEqual(True, SATSolver(all_clauses).solve())

    def test_10_color(self):
        colors = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
        edges = [
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

        vertices = set()
        for edge in edges:
            v1, v2 = edge
            vertices.add(v1)
            vertices.add(v2)

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

        self.assertEqual(True, SATSolver(all_clauses).solve())

    def test_insane_color(self):
        # When colors are 1 ... 300:
        # Variables:  3588 , clauses:  543594
        # Ran 1 test in 16.648s
        # When colors are 1 ... 500:
        # Variables:  5988 , clauses:  1505994
        # Ran 1 test in 49.422s
        colors = list(range(1, 100))
        edges = [
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

        vertices = set()
        for edge in edges:
            v1, v2 = edge
            vertices.add(v1)
            vertices.add(v2)

        variables = len(colors) * len(vertices)
        clause_count = 0
        clause_count += len(vertices)
        clause_count += len(vertices) * int(comb(len(colors), 2))
        clause_count += len(edges) * len(colors)
        print("Variables: ", variables, ", clauses: ", clause_count)

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

        self.assertEqual(True, SATSolver(all_clauses).solve())


if __name__ == '__main__':
    unittest.main()
