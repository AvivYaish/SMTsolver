import numpy as np


class LinearSolver:
    Bland = "Bland"
    Dantzig = "Dantzig"
    FirstPositive = "FirstPositive"

    def __init__(self, A, b, c, entering_selection_rule=Bland, auxiliary=False):
        self._rows = np.size(A, 0)
        self._cols = np.size(A, 1)
        self._A_N = A.astype(np.float64).copy()
        self._B = np.identity(self._rows, dtype=np.float64)
        self._x_N_vars = np.arange(self._cols)
        self._x_B_vars = np.arange(self._rows) + self._cols
        self._x_B_star = b.astype(np.float64).copy()
        self._c_N = c.astype(np.float64).copy()
        self._c_B = np.zeros(self._rows, dtype=np.float64)

        if entering_selection_rule == LinearSolver.Bland:
            self._entering_selection_rule = self._bland_rule
        elif entering_selection_rule == LinearSolver.Dantzig:
            self._entering_selection_rule = self._dantzig_rule
        elif entering_selection_rule == LinearSolver.FirstPositive:
            self._entering_selection_rule = self._first_positive_rule

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
        entering_col = self._choose_entering_col(y)
        if entering_col == -1:
            return np.matmul(self._c_B, self._x_B_star)

        d = self._ftran(self._B, self._A_N[:, entering_col])
        leaving_col, t = self._choose_leaving_col(d)
        if t == np.inf:
            return np.inf

        self._pivot(entering_col, leaving_col, t, d)
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

    def _first_positive_rule(self, cur_objective_func):
        for idx in range(len(cur_objective_func)):
            if cur_objective_func[idx] > 0:
                return idx
        return -1

    def _bland_rule(self, cur_objective_func):
        return np.where(cur_objective_func > 0, self._x_N_vars, np.inf).argmin()

    def _dantzig_rule(self, cur_objective_func):
        return np.argmax(cur_objective_func)

    def _choose_entering_col(self, y):
        cur_objective_func = self._c_N - np.matmul(y, self._A_N)
        positive_indices = cur_objective_func > 0
        if not np.any(positive_indices):
            return -1
        return self._entering_selection_rule(cur_objective_func)

    def _choose_leaving_col(self, d):
        all_ts = self._x_B_star / d
        if np.all(all_ts <= 0):
            return -1, np.inf
        # Cool numpy method for finding smallest positive value, found at:
        # https://stackoverflow.com/questions/55769522/how-to-find-maximum-negative-and-minimum-positive-number-in-a-numpy-array
        min_ratio = np.where(all_ts > 0, all_ts, np.inf).min()
        # Choose var which achieves min-ratio and has the minimal index
        min_ratio_idx = np.where(all_ts == min_ratio, self._x_B_vars, np.inf).argmin()
        return min_ratio_idx, min_ratio

    @staticmethod
    def _btran(B, c_B):
        """
        :return: the solution 'y' of yB = c_B
        """
        return np.matmul(c_B, np.linalg.inv(B))

    @staticmethod
    def _ftran(B, a):
        return np.linalg.solve(B, a)
