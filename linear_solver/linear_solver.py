import numpy as np
from numba import jit


class LinearSolver:

    def __init__(self, A, b, c):
        self._rows = A.shape[0]
        self._A_N = A.astype(np.float64).copy()
        self._B = np.identity(self._rows, dtype=np.float64)
        self._c_N = c.astype(np.float64).copy()
        self._c_B = np.zeros(self._rows, dtype=np.float64)
        self._x_B_star = b.astype(np.float64).copy()

    """
    
    """
    def solve(self):
        """
        >>> A = np.array([[1, 1, 2], [2, 0, 3], [2, 1, 3]])
        >>> b = np.array([4, 5, 7])
        >>> c = np.array([3, 2, 4])
        >>> solver = LinearSolver(A, b, c)
        >>> solver.solve()
        10.5
        >>> A = np.array([[3, 4], [6, 1]])
        >>> b = np.array([6, 3])
        >>> c = np.array([2, 1])
        >>> solver = LinearSolver(A, b, c)
        >>> solver.solve()
        1.8571428571428572
        >>> A = np.array([[3, 2, 1, 2], [1, 1, 1, 1], [4, 3, 3, 4]])
        >>> b = np.array([225, 117, 420])
        >>> c = np.array([19, 13, 12, 17])
        >>> solver = LinearSolver(A, b, c)
        >>> solver.solve()
        1827.0
        """
        while True:
            result = self._single_iteration()
            if result is not None:
                return result
        return False

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

        # Update current assignments and objective function
        self._x_B_star -= t * d
        self._x_B_star[B_col_idx] = t
        self._c_B[B_col_idx], self._c_N[A_col_idx] = self._c_N[A_col_idx], self._c_B[B_col_idx]
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
    def _minimal_positive_index(arr):
        min_idx = -1
        for idx in range(len(arr)):
            if (arr[idx] > 0) and ((min_idx == -1) or (arr[idx] < arr[min_idx])):
                min_idx = idx
        return min_idx

    @staticmethod
    def _choose_leaving_var(x_B, d):
        all_ts = x_B / d
        largest_t_idx = LinearSolver._minimal_positive_index(all_ts)
        return largest_t_idx, all_ts[largest_t_idx]

    @staticmethod
    def _btran(B, c_B):
        """
        :return: the solution 'y' of yB = c_B
        """
        return np.matmul(c_B, np.linalg.inv(B))

    @staticmethod
    def _ftran(B, a):
        return np.linalg.solve(B, a)
