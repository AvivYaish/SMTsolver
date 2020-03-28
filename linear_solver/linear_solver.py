import numpy as np
from numba import jit


class LinearSolver:

    def __init__(self, A, b, c):
        self._rows = np.size(A, 0)
        self._cols = np.size(A, 1)
        self._A_N = A.astype(np.float64).copy()
        self._B = np.identity(self._rows, dtype=np.float64)
        self._x_N_vars = np.arange(self._cols)
        self._x_B_vars = np.arange(self._rows) + self._cols
        self._x_B_star = b.astype(np.float64).copy()
        self._c_N = c.astype(np.float64).copy()
        self._c_B = np.zeros(self._rows, dtype=np.float64)

    @staticmethod
    def _solve_auxiliary_problem(A, b):
        new_var = np.size(A, 1)     # Because that number is unused
        new_A = np.concatenate((A, -np.ones((np.size(A, 0), 1))))
        solver = LinearSolver(new_A, b, np.array([-new_var]))
        solver.solve()
        if solver.get_assignment()[new_var] != 0:
            return None
        return solver._x_B_vars

    def get_assignment(self):
        assignment = {var: 0 for var in range(self._cols)}
        for var, value in zip(self._x_B_vars, self._x_B_star):
            if var < self._cols:
                assignment[var] = value
        return assignment

    def solve(self):
        """

        """
        if not np.all(self._c_B >= 0):
            auxiliary_basic_vars = LinearSolver._solve_auxiliary_problem(self._A_N, self._x_B_star)
            if auxiliary_basic_vars is None:
                return None

        while True:
            result = self._single_iteration()
            if result is not None:
                return result

    def _single_iteration(self):
        y = self._btran(self._B, self._c_B)
        A_col_idx = self._choose_entering_var(self._A_N, y, self._c_N)
        if A_col_idx == -1:
            return np.matmul(self._c_B, self._x_B_star)

        d = self._ftran(self._B, self._A_N[:, A_col_idx])
        B_col_idx, t = self._choose_leaving_var(self._x_B_star, d)
        if B_col_idx == -1:
            return float('inf')

        # Update the matrices
        A_col = self._A_N[:, A_col_idx].copy()
        self._A_N[:, A_col_idx] = self._B[:, B_col_idx]
        self._B[:, B_col_idx] = A_col

        # Update the assignment
        self._x_B_star -= t * d
        self._x_B_star[B_col_idx] = t

        # Update the objective function and index placement
        self._c_B[B_col_idx], self._c_N[A_col_idx] = self._c_N[A_col_idx], self._c_B[B_col_idx]
        self._x_B_vars[B_col_idx], self._x_N_vars[A_col_idx] = self._x_N_vars[A_col_idx], self._x_B_vars[B_col_idx]
        return None

    @staticmethod
    def _first_positive_index(arr):
        # Super-fast numba implementation, as seen in:
        # https://stackoverflow.com/questions/16243955/numpy-first-occurrence-of-value-greater-than-existing-value
        for idx in range(len(arr)):
            if arr[idx] >= 0:
                return idx
        return -1

    @staticmethod
    def _choose_entering_var(A_N, y, c_N):
        # Bland's rule
        return LinearSolver._first_positive_index(c_N - np.matmul(y, A_N))

    @staticmethod
    def _choose_leaving_var(x_B, d):
        all_ts = x_B / d
        # Cool numpy method for finding smallest positive value, found at:
        # https://stackoverflow.com/questions/55769522/how-to-find-maximum-negative-and-minimum-positive-number-in-a-numpy-array
        largest_t_idx = np.where(all_ts > 0, all_ts, np.inf).argmin()
        largest_t_val = all_ts[largest_t_idx]
        if largest_t_val == np.inf:
            # If the minimal positive index is inf, the solution is unbounded
            largest_t_idx = -1
        return largest_t_idx, largest_t_val

    @staticmethod
    def _btran(B, c_B):
        """
        :return: the solution 'y' of yB = c_B
        """
        return np.matmul(c_B, np.linalg.inv(B))

    @staticmethod
    def _ftran(B, a):
        return np.linalg.solve(B, a)
