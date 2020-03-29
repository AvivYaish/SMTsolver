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

    def _solve_auxiliary_problem(self) -> bool:
        new_A = np.concatenate((-np.ones((self._rows, 1)), self._A_N), axis=1)
        new_c = np.concatenate((np.array([-1]), np.zeros(self._cols)))
        aux_solver = LinearSolver(new_A, self._x_B_star, new_c, auxiliary=True)
        aux_solver.solve()
        # The auxiliary problem had an additional first variable, its ID is 0
        if aux_solver.get_assignment()[0] != 0:
            return False

        # Can prove the new variable is not in the basis.
        self._x_B_vars = aux_solver._x_B_vars - 1   # All variables (including slack ones) are shifted by 1
        self._x_B_star = aux_solver._x_B_star
        self._B = aux_solver._B

        # Remove the new variable from all data structures
        new_var_idx = np.argmin(aux_solver._x_N_vars)
        self._x_N_vars = np.delete(aux_solver._x_N_vars - 1, new_var_idx)
        self._A_N = np.delete(aux_solver._A_N, new_var_idx, axis=1)

        # Reorder c_B and c_N accordingly
        for idx, var in enumerate(self._x_B_vars):
            if var < self._cols:  # var is not slack
                self._c_B[idx] = self._c_N[var]

        new_c_N = np.zeros(self._cols, dtype=np.float64)
        for idx, var in enumerate(self._x_N_vars):
            if var >= self._cols:   # var is slack
                new_c_N[idx] = 0
            else:
                new_c_N[idx] = self._c_N[var]
        self._c_N = new_c_N
        return True

    def get_assignment(self):
        assignment = {var: 0 for var in range(self._cols)}
        for var, value in zip(self._x_B_vars, self._x_B_star):
            if var in assignment:
                assignment[var] = value
        return assignment

    def _initial_auxiliary_step(self):
        # The entering variable is always the new variable created for the
        # aux. problem, so a = A_N[:, 0] = [-1, ..., -1].
        # The leaving variable is the one corresponding to the minimal b_i.
        # Because this is the first iteration, the B matrix is I,
        # so d = a * (B^-1) = a * (I^-1) = a * I = a, thus t = -min_b_i
        entering_var, leaving_var = 0, np.argmin(self._x_B_star)
        t, d = -self._x_B_star[leaving_var], self._A_N[:, entering_var].copy()
        self._pivot(entering_var, leaving_var, t, d)

    def solve(self):
        """

        """
        if (not np.all(self._x_B_star >= 0)) and (not self._solve_auxiliary_problem()):
            return None

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

        # Update the objective function
        self._c_B[leaving_var], self._c_N[entering_var] = self._c_N[entering_var], self._c_B[leaving_var]

        # Update indices
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
