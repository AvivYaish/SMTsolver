import pytest
import numpy as np
from linear_solver.linear_solver import LinearSolver


class TestLinearSolver:
    @staticmethod
    def test_solve():
        # Using some example problems from lecture 12, HW2,
        # and https://cbom.atozmath.com/example/CBOM/Simplex.aspx?he=e&q=rsm
        A = np.array([[1, 1, 2], [2, 0, 3], [2, 1, 3]])
        b = np.array([4, 5, 7])
        c = np.array([3, 2, 4])
        solver = LinearSolver(A, b, c)
        assert solver.solve() == 10.5
        assert solver.get_assignment() == {0: 2.5, 1: 1.5, 2: 0}

        A = np.array([[3, 2, 1, 2], [1, 1, 1, 1], [4, 3, 3, 4]])
        b = np.array([225, 117, 420])
        c = np.array([19, 13, 12, 17])
        solver = LinearSolver(A, b, c)
        assert solver.solve() == 1827.0
        assert solver.get_assignment() == {0: 38.99999999999998, 1: 0, 2: 47.99999999999998, 3: 30.000000000000043}

        A = np.array([[3, 4], [6, 1]])
        b = np.array([6, 3])
        c = np.array([2, 1])
        solver = LinearSolver(A, b, c)
        assert solver.solve() == 1.8571428571428572
        assert solver.get_assignment() == {0: 0.2857142857142857, 1: 1.2857142857142858}

        A = np.array([[1, 0], [0, 1], [3, 2]])
        b = np.array([4, 6, 18])
        c = np.array([3, 5])
        solver = LinearSolver(A, b, c)
        assert solver.solve() == 36.0
        assert solver.get_assignment() == {0: 2.0, 1: 6.0}
