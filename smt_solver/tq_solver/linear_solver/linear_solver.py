from smt_solver.solver.solver import Solver
from itertools import chain
import numpy as np


class LinearSolver(Solver):
    Bland = "Bland"
    Dantzig = "Dantzig"
    FirstPositive = "FirstPositive"

    def __init__(self, a_matrix, b, c, entering_selection_rule=Bland, auxiliary=False):
        super().__init__()
        self._aux_solver: LinearSolver = None
        self._score = np.float64(0.0)
        self._rows = np.size(a_matrix, 0)
        self._cols = np.size(a_matrix, 1)
        self._a_matrix_n = a_matrix.astype(np.float64).copy()
        self._a_matrix_b = np.identity(self._rows, dtype=np.float64)
        self._x_n_vars = np.arange(self._cols)
        self._x_n_star = np.zeros(self._cols)
        self._x_b_vars = np.arange(self._rows) + self._cols
        self._x_b_star = b.astype(np.float64).copy()
        self._c_n = c.astype(np.float64).copy()
        self._c_b = np.zeros(self._rows, dtype=np.float64)

        if entering_selection_rule == LinearSolver.Bland:
            self._entering_selection_rule = self._bland_rule
        elif entering_selection_rule == LinearSolver.Dantzig:
            self._entering_selection_rule = self._dantzig_rule
        elif entering_selection_rule == LinearSolver.FirstPositive:
            self._entering_selection_rule = self._first_positive_rule

        if auxiliary:
            self._initial_auxiliary_step()

    def _solve_auxiliary_problem(self) -> bool:
        new_a_matrix = np.concatenate((-np.ones((self._rows, 1)), self._a_matrix_n), axis=1)
        new_c = np.concatenate((np.array([-1]), np.zeros(self._cols)))
        self._aux_solver = LinearSolver(new_a_matrix, self._x_b_star, new_c, auxiliary=True)
        self._aux_solver.solve()
        # The auxiliary problem had an additional first variable, its ID is 0
        return self._aux_solver.get_assignment()[0] == 0

    def _update_to_match_auxiliary_problem(self):
        # Can prove the new variable is not in the basis.
        self._x_b_vars = self._aux_solver._x_b_vars - 1   # All variables (including slack ones) are shifted by 1
        self._x_b_star = self._aux_solver._x_b_star
        self._a_matrix_b = self._aux_solver._a_matrix_b

        # Remove the new variable from all data structures
        new_var_idx = np.argmin(self._aux_solver._x_n_vars)
        self._x_n_vars = np.delete(self._aux_solver._x_n_vars - 1, new_var_idx)
        self._a_matrix_n = np.delete(self._aux_solver._a_matrix_n, new_var_idx, axis=1)

        # Reorder c_B and c_N accordingly
        for idx, var in enumerate(self._x_b_vars):
            if var < self._cols:  # var is not slack
                self._c_b[idx] = self._c_n[var]

        new_c_n = np.zeros(self._cols, dtype=np.float64)
        for idx, var in enumerate(self._x_n_vars):
            if var >= self._cols:   # var is slack
                new_c_n[idx] = 0
            else:
                new_c_n[idx] = self._c_n[var]
        self._c_n = new_c_n

    def get_assignment(self):
        assignment = {var: 0 for var in range(self._cols)}
        for var, value in chain(zip(self._x_b_vars, self._x_b_star), zip(self._x_n_vars, self._x_n_star)):
            if var in assignment:
                assignment[var] = value
        return assignment

    def _initial_auxiliary_step(self):
        # The entering variable is always the new variable created for the
        # aux. problem, so a = A_N[:, 0] = [-1, ..., -1].
        # The leaving variable is the one corresponding to the minimal b_i.
        # Because this is the first iteration, the B matrix is I,
        # so d = a * (B^-1) = a * (I^-1) = a * I = a, thus t = -min_b_i
        entering_var, leaving_var = 0, np.argmin(self._x_b_star)
        t, d = -self._x_b_star[leaving_var], self._a_matrix_n[:, entering_var].copy()
        self._pivot(entering_var, leaving_var, t, d)

    def is_sat(self) -> bool:
        return np.all(self._x_b_star >= 0) or self._solve_auxiliary_problem()

    def get_score(self) -> np.float64:
        return self._score

    def solve(self) -> bool:
        if not self.is_sat():
            return False
        elif self._aux_solver is not None:
            self._update_to_match_auxiliary_problem()

        while True:
            result = self._single_iteration()
            if result is not None:
                self._score = result
                return True

    def _single_iteration(self):
        y = self._btran()
        entering_col = self._choose_entering_col(y)
        if entering_col == -1:
            return np.matmul(self._c_b, self._x_b_star)

        d = self._ftran(entering_col)
        leaving_col, t = self._choose_leaving_col(d)
        if t == np.inf:
            self._x_n_star[entering_col] = np.inf
            return np.inf

        self._pivot(entering_col, leaving_col, t, d)
        return None

    def _pivot(self, entering_var: int, leaving_var: int, t, d):
        # Update the matrices
        entering_col = self._a_matrix_n[:, entering_var].copy()
        self._a_matrix_n[:, entering_var] = self._a_matrix_b[:, leaving_var]
        self._a_matrix_b[:, leaving_var] = entering_col

        # Update the objective function
        self._c_b[leaving_var], self._c_n[entering_var] = self._c_n[entering_var], self._c_b[leaving_var]

        # Update indices
        self._x_b_vars[leaving_var], self._x_n_vars[entering_var] = \
            self._x_n_vars[entering_var], self._x_b_vars[leaving_var]

        # Update the assignment
        self._x_b_star -= t * d
        self._x_b_star[leaving_var] = t

    @staticmethod
    def _first_positive_rule(cur_objective_func):
        for idx in range(len(cur_objective_func)):
            if cur_objective_func[idx] > 0:
                return idx
        return -1

    def _bland_rule(self, cur_objective_func):
        return np.where(cur_objective_func > 0, self._x_n_vars, np.inf).argmin()

    @staticmethod
    def _dantzig_rule(cur_objective_func):
        return np.argmax(cur_objective_func)

    def _choose_entering_col(self, y):
        cur_objective_func = self._c_n - np.matmul(y, self._a_matrix_n)
        positive_indices = cur_objective_func > 0
        if not np.any(positive_indices):
            return -1
        return self._entering_selection_rule(cur_objective_func)

    def _choose_leaving_col(self, d):
        all_ts = self._x_b_star / d
        if np.all(all_ts <= 0):
            return -1, np.inf
        # Cool numpy method for finding smallest positive value, found at:
        # https://stackoverflow.com/questions/55769522/how-to-find-maximum-negative-and-minimum-positive-number-in-a-numpy-array
        min_ratio = np.where(all_ts > 0, all_ts, np.inf).min()
        # Choose var which achieves min-ratio and has the minimal index
        min_ratio_idx = np.where(all_ts == min_ratio, self._x_b_vars, np.inf).argmin()
        return min_ratio_idx, min_ratio

    def _btran(self):
        """
        :return: the solution 'y' of yB = c_B
        """
        return np.matmul(self._c_b, np.linalg.inv(self._a_matrix_b))

    def _ftran(self, entering_col):
        return np.linalg.solve(self._a_matrix_b, self._a_matrix_n[:, entering_col])
