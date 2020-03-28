import numpy as np
from numba import jit


class LinearSolver:

    def __init__(self, A, b, c, auxiliary=False):
        self._rows = np.size(A, 0)
        self._cols = np.size(A, 1)
        self._A_N = A.astype(np.float64).copy()
        self._B = np.identity(self._rows, dtype=np.float64)
        self._x_N_vars = np.arange(self._cols)
        self._x_B_vars = np.arange(self._rows) + self._cols
        self._x_B_star = b.astype(np.float64).copy()
        self._c_N = c.astype(np.float64).copy()
        self._c_B = np.zeros(self._rows, dtype=np.float64)

        if auxiliary:
            self._initial_auxiliary_step()

    @staticmethod
    def _solve_auxiliary_problem(A, b):
        new_A = np.concatenate((-np.ones((np.size(A, 0), 1)), A), axis=1)
        new_c = np.concatenate((np.array([-1]), np.zeros(np.size(A, 1))))
        solver = LinearSolver(new_A, b, new_c, auxiliary=True)
        solver.solve()
        assignment = solver.get_assignment()
        # new_var = 0
        if assignment[0] != 0:
            return None
        assignment.pop(0)
        # The auxiliary problem had an additional first variable,
        # so all variables (including slack ones) are shifted by 1
        return solver._x_B_vars - 1, {(var - 1): assignment[var] for var in assignment}

    def get_assignment(self):
        assignment = {var: 0 for var in range(self._cols)}
        for var, value in zip(self._x_B_vars, self._x_B_star):
            if var < self._cols:
                assignment[var] = value
        return assignment

    def _initial_auxiliary_step(self):
        # The entering variable is always the new variable created for the aux. problem
        # The leaving variable is the one corresponding to the minimal b_i
        # Because this is the first iteration, the B matrix is the identity,
        # so d = c_B * (B^-1) = A_N[:, 0] = [-1, ..., -1]
        # And thus t = -min_b_i
        entering_var, leaving_var = 0, np.argmin(self._x_B_star)
        t, d = -self._x_B_star[leaving_var], self._A_N[:, entering_var].copy()
        self._pivot(entering_var, leaving_var, t, d)

    def solve(self):
        """

        """
        if not np.all(self._x_B_star >= 0):
            auxiliary_basic_vars, assignment = LinearSolver._solve_auxiliary_problem(self._A_N, self._x_B_star)
            if auxiliary_basic_vars is None:
                return None
            for var in auxiliary_basic_vars:
                pass

        while True:
            result = self._single_iteration()
            if result is not None:
                return result

    def _single_iteration(self):
        y = self._btran(self._B, self._c_B)
        entering_var = self._choose_entering_var(self._A_N, y, self._c_N)
        if entering_var == -1:
            return np.matmul(self._c_B, self._x_B_star)

        d = self._ftran(self._B, self._A_N[:, entering_var])
        leaving_var, t = self._choose_leaving_var(self._x_B_star, d)
        if leaving_var == -1:
            return float('inf')

        self._pivot(entering_var, leaving_var, t, d)
        return None

    def _pivot(self, entering_var: int, leaving_var: int, t, d):
        # Update the matrices
        entering_col = self._A_N[:, entering_var].copy()
        self._A_N[:, entering_var] = self._B[:, leaving_var]
        self._B[:, leaving_var] = entering_col

        # Update the objective function and index placement
        self._c_B[leaving_var], self._c_N[entering_var] = self._c_N[entering_var], self._c_B[leaving_var]
        self._x_B_vars[leaving_var], self._x_N_vars[entering_var] = \
            self._x_N_vars[entering_var], self._x_B_vars[leaving_var]

        # Update the assignment
        self._x_B_star -= t * d
        self._x_B_star[leaving_var] = t

    @staticmethod
    def _first_positive_index(arr):
        for idx in range(len(arr)):
            if arr[idx] > 0:
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
