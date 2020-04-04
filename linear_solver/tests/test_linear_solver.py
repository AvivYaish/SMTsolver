import pytest
import numpy as np
from linear_solver.linear_solver import LinearSolver


class TestLinearSolver:
    @staticmethod
    @pytest.mark.parametrize("entering_selection_rule", [LinearSolver.FirstPositive, LinearSolver.Dantzig,
                                                         LinearSolver.Bland])
    def test_solve(entering_selection_rule):
        # Using some example problems from lecture 12, HW2,
        # and https://cbom.atozmath.com/example/CBOM/Simplex.aspx?he=e&q=rsm
        A = np.array([[1, 1, 2], [2, 0, 3], [2, 1, 3]])
        b = np.array([4, 5, 7])
        c = np.array([3, 2, 4])
        solver = LinearSolver(A, b, c, entering_selection_rule=entering_selection_rule)
        assert solver.solve()
        assert solver.get_assignment() == {0: pytest.approx(2.5), 1: pytest.approx(1.5), 2: pytest.approx(0)}

        A = np.array([[3, 2, 1, 2], [1, 1, 1, 1], [4, 3, 3, 4]])
        b = np.array([225, 117, 420])
        c = np.array([19, 13, 12, 17])
        solver = LinearSolver(A, b, c, entering_selection_rule=entering_selection_rule)
        assert solver.solve()
        assert solver.get_assignment() == {0: pytest.approx(39), 1: pytest.approx(0), 2: pytest.approx(48),
                                           3: pytest.approx(30)}

        A = np.array([[3, 4], [6, 1]])
        b = np.array([6, 3])
        c = np.array([2, 1])
        solver = LinearSolver(A, b, c, entering_selection_rule=entering_selection_rule)
        assert solver.solve()
        assert solver.get_assignment() == {0: pytest.approx(0.2857142857142857), 1: pytest.approx(1.2857142857142858)}

        A = np.array([[1, 0], [0, 1], [3, 2]])
        b = np.array([4, 6, 18])
        c = np.array([3, 5])
        solver = LinearSolver(A, b, c, entering_selection_rule=entering_selection_rule)
        assert solver.solve()
        assert solver.get_assignment() == {0: pytest.approx(2.0), 1: pytest.approx(6.0)}

        A = np.array([[-1, 1], [-2, -2], [-1, 4]])
        b = np.array([-1, -6, 2])
        c = np.array([1, 3])
        solver = LinearSolver(A, b, c, entering_selection_rule=entering_selection_rule)
        assert solver.solve()
        assert solver.get_score() == np.inf

        A = np.array([[1, -1, 1], [-2, 1, 0], [0, 1, -2]])
        b = np.array([5, 3, 5])
        c = np.array([0, 2, 1])
        solver = LinearSolver(A, b, c, entering_selection_rule=entering_selection_rule)
        assert solver.solve()
        assert solver.get_assignment() == {0: pytest.approx(1.0), 1: pytest.approx(5.0), 2: np.inf}
        assert solver.get_score() == np.inf
