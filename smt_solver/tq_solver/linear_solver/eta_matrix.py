import numpy as np


class EtaMatrix:
    def __init__(self, col_idx: int, col_vals: np.array):
        """
        :param col_idx: column count starts from 0.
        :param col_vals: the values of the column, as a 1 dimensional numpy array.
        """
        self._col_idx = col_idx
        self._col_vals = col_vals.astype(np.float64)

    def invert(self):
        """
        :return: the inversion of this matrix.
        >>> m = EtaMatrix(1, np.array([-4, 3, 2]))
        >>> m_inverse = m.invert()
        >>> m_inverse._col_idx == 1
        True
        >>> np.all(np.isclose(m_inverse._col_vals, np.array([ 1.33333333,  0.33333333, -0.66666667])))
        True
        """
        inverse_diag_element = np.float64(1 / self._col_vals[self._col_idx])
        inversion = EtaMatrix(self._col_idx, self._col_vals * -inverse_diag_element)
        inversion._col_vals[self._col_idx] = inverse_diag_element
        return inversion

    def solve_left_mult(self, y: np.array):
        """
        Solves a formula of the form: [x1, ..., xn] * self = y
        >>> m = EtaMatrix(1, np.array([-4, 3, 2]))
        >>> m.solve_left_mult(np.array([1, 2, 3]))
        array([1., 0., 3.])
        >>> m.solve_left_mult(np.array([3, 2, 1]))
        array([3., 4., 1.])
        """
        result = y.astype(np.float64)
        result[self._col_idx] = np.float64(0)
        result[self._col_idx] = (np.matmul(-self._col_vals, result) + y[self._col_idx]) / self._col_vals[self._col_idx]
        return result

    def solve_right_mult(self, y: np.array):
        """
        Solves a formula of the form: [x1, ..., xn] * self = y
        >>> m = EtaMatrix(1, np.array([-4., 3., 2.]))
        >>> m.solve_right_mult(np.array([1., 2., 3.]))
        array([3.66666667, 0.66666667, 1.66666667])
        """
        result = y.astype(np.float64)
        eta_val = np.float64(y[self._col_idx] / self._col_vals[self._col_idx])
        result -= self._col_vals * eta_val
        result[self._col_idx] = eta_val
        return result
