from smt_solver.tq_solver.linear_solver.eta_matrix import EtaMatrix
import numpy as np


class LUFactorization:
    """
    Based on a small JS project I've made in 2016:
    https://github.com/AvivYaish/LUM/
    """
    ROW_AXIS = 0
    COL_AXIS = 1

    @staticmethod
    def generate_p(matrix):
        """
        Moving rows such that each column's max value is on the diagonal ensures us the
        resulting matrix has a LU decomposition. The function will search for the max
        value in each column and will generate the P matrix.
        :return: a tuple: (the pivot matrix 'p', 'matrix' after pivoting)

        >>> matrix = np.array([[3, 1, 0], [1, 1, 0], [4, 3, 1]])
        >>> p = LUFactorization.generate_p(matrix)
        >>> np.all(np.matmul(p, matrix) == np.array([[4, 3, 1], [3, 1, 0], [1, 1, 0]]))
        True
        """
        # If matrix is n*n, runs in O(n*n), assuming that slicing of numpy arrays is O(1)
        p = np.identity(np.size(matrix, LUFactorization.ROW_AXIS))
        for col in np.arange(np.size(matrix, LUFactorization.COL_AXIS)):
            max_row = np.argmax(matrix[col:, col]) + col
            p[[col, max_row], :] = p[[max_row, col], :]
        return p

    @staticmethod
    def lu_decomposition(matrix):
        """
        >>> matrix = np.array([[3, 1, 0], [1, 1, 0], [4, 3, 1]])
        >>> ls, us = LUFactorization.lu_decomposition(np.matmul(LUFactorization.generate_p(matrix), matrix))
        >>> l, u = np.identity(3), np.identity(3)
        >>> for cur_l, cur_u in zip(reversed(ls), us):
        ...     l = np.matmul(cur_l.invert().get_full_matrix(), l)
        ...     u = np.matmul(cur_u.get_full_matrix(), u)
        ... np.matmul(l, u)
        """
        # Could probably speed this up using nifty numpy tricks, but this still achieves the best theoretical run-time
        row_num = np.size(matrix, LUFactorization.COL_AXIS)
        cur_matrix, l_matrices, u_matrices = np.copy(matrix), [], []
        for col_idx, cur_eta_col in enumerate(np.identity(row_num)):
            for row_idx in np.arange(col_idx + 1, row_num):
                if cur_matrix[row_idx, col_idx] != 0:
                    cur_eta_col[row_idx] = -cur_matrix[row_idx, col_idx] / cur_matrix[col_idx, col_idx]
                    cur_matrix[row_idx] += cur_eta_col[row_idx] * cur_matrix[col_idx]
            l_matrices.append(EtaMatrix(col_idx, cur_eta_col))

        for idx, col_idx in enumerate(cur_matrix.T):
            u_matrices.append(EtaMatrix(idx, col_idx))
        return l_matrices, u_matrices

    @staticmethod
    def plu_decomposition(matrix):
        """
        """
        p = LUFactorization.generate_p(matrix)
        return p, LUFactorization.lu_decomposition(np.matmul(p, matrix))
