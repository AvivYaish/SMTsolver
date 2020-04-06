from smt_solver.tq_solver.linear_solver.alebgra_utils.eta_matrix import EtaMatrix
import numpy as np


class LUFactorization:
    """
    Based on a small JS project I've made in 2016:
    https://github.com/AvivYaish/LUM/
    """

    @staticmethod
    def generate_p(matrix):
        """
        Moving rows such that each column's max value is on the diagonal ensures us the
        resulting matrix has a LU decomposition. The function will search for the max
        value in each column and will generate the P matrix.
        :return: a tuple: (pivot_matrix, pivot_list), where pivot_list is as a list of (row1, row2) tuples,
        where row1 and row2 were switched at that step.
        """
        # cur_matrix = np.copy(matrix)
        # # If matrix is n*n, runs in O(n*n), assuming that slicing of numpy arrays is O(1)
        # pivot_matrix, pivot_list = np.identity(np.size(matrix, 0)), []
        # for col in np.arange(np.size(matrix, 1)):
        #     max_row = np.argmax(np.abs(cur_matrix[col:, col])) + col
        #     if col != max_row:
        #         pivot_matrix[[col, max_row], :] = pivot_matrix[[max_row, col], :]
        #         cur_matrix[[col, max_row], :] = cur_matrix[[max_row, col], :]
        #         pivot_list.append((col, max_row))
        col_num = np.size(matrix, 1)  # square matrix, so this is equal to the row number, too
        cur_matrix, pivot_matrix, pivot_list = np.copy(matrix), np.identity(col_num), []

        for col_idx, cur_eta_col in enumerate(np.identity(col_num)):
            max_row = np.argmax(np.abs(cur_matrix[col_idx:, col_idx])) + col_idx
            if col_idx != max_row:
                pivot_matrix[[col_idx, max_row], :] = pivot_matrix[[max_row, col_idx], :]
                cur_matrix[[col_idx, max_row], :] = cur_matrix[[max_row, col_idx], :]
                pivot_list.append((col_idx, max_row))

            for row_idx in np.arange(col_idx + 1, col_num):
                if cur_matrix[row_idx, col_idx] != 0:
                    cur_eta_col[row_idx] = -cur_matrix[row_idx, col_idx] / cur_matrix[col_idx, col_idx]
                    cur_matrix[row_idx] = np.add(cur_matrix[row_idx], cur_eta_col[row_idx] * cur_matrix[col_idx])

        return pivot_matrix, pivot_list

    @staticmethod
    def pivot_matrix(pivot_list, matrix, reverse=False):
        """
        :return: the matrix, after pivoting in-place according to 'pivots'.
        """
        if reverse:
            pivot_iterable = reversed(pivot_list)
        else:
            pivot_iterable = pivot_list
        for row1, row2 in pivot_iterable:
            matrix[[row1, row2], :] = matrix[[row2, row1], :]
        return matrix

    @staticmethod
    def pivot_array(pivot_list, array, reverse=False, in_place=True):
        """
        :return: the array, after pivoting according to 'pivots'.
        """
        if in_place:
            array_to_return = array
        else:
            array_to_return = np.copy(array)
        if reverse:
            pivot_iterable = reversed(pivot_list)
        else:
            pivot_iterable = pivot_list
        for row1, row2 in pivot_iterable:
            array_row1 = np.copy(array_to_return[row1])
            array_to_return[row1] = array_to_return[row2]
            array_to_return[row2] = array_row1
        return array_to_return

    @staticmethod
    def lu_factorization(matrix):
        """
        :return: An iterable(L_1^-1, L_2^-1, ..., U_N, U_N-1, ...) such that
        matrix = L_1^-1 * ... * L_N^-1 * U_N * ... U_1, and all L_i^-1, U_i are eta matrices.
        """
        # Could probably speed this up using nifty numpy tricks,
        # but this still achieves the best theoretical run-time
        col_num = np.size(matrix, 1)    # square matrix, so this is equal to the row number, too
        cur_matrix, matrices = np.copy(matrix), []

        # Create L matrices
        for col_idx, cur_eta_col in enumerate(np.identity(col_num)):
            for row_idx in np.arange(col_idx + 1, col_num):
                if cur_matrix[row_idx, col_idx] != 0:
                    cur_eta_col[row_idx] = -cur_matrix[row_idx, col_idx] / cur_matrix[col_idx, col_idx]
                    cur_matrix[row_idx] += cur_eta_col[row_idx] * cur_matrix[col_idx]
            matrices.append(EtaMatrix(col_idx, cur_eta_col).invert())

        # Create U matrices
        for col_idx, cur_eta_col in enumerate(reversed(cur_matrix.T)):
            matrices.append(EtaMatrix(col_num - col_idx - 1, cur_eta_col))
        return matrices

    @staticmethod
    def plu_factorization(matrix):
        """
        :return: (pivot_matrix, pivot_list) and an iterable(L_1^-1, L_2^-1, ..., U_N, U_N-1, ...) such that
        pivot_matrix * matrix = L_1^-1 * ... * L_N^-1 * U_N * ... U_1, and all L_i^-1, U_i are eta matrices.
        """
        # col_num = np.size(matrix, 1)    # square matrix, so this is equal to the row number, too
        # cur_matrix, matrices, pivot_matrix, pivot_list = np.copy(matrix), [], np.identity(col_num), []
        #
        # # Create L matrices
        # for col_idx, cur_eta_col in enumerate(np.identity(col_num)):
        #     max_row = np.argmax(np.abs(cur_matrix[col_idx:, col_idx])) + col_idx
        #     if col_idx != max_row:
        #         pivot_matrix[[col_idx, max_row], :] = pivot_matrix[[max_row, col_idx], :]
        #         cur_matrix[[col_idx, max_row], :] = cur_matrix[[max_row, col_idx], :]
        #         pivot_list.append((col_idx, max_row))
        #
        #     for row_idx in np.arange(col_idx + 1, col_num):
        #         if cur_matrix[row_idx, col_idx] != 0:
        #             cur_eta_col[row_idx] = -cur_matrix[row_idx, col_idx] / cur_matrix[col_idx, col_idx]
        #             cur_matrix[row_idx] = np.add(cur_matrix[row_idx], cur_eta_col[row_idx] * cur_matrix[col_idx])
        #     matrices.append(EtaMatrix(col_idx, cur_eta_col).invert())
        #
        # # Create U matrices
        # for col_idx, cur_eta_col in enumerate(reversed(cur_matrix.T)):
        #     matrices.append(EtaMatrix(col_num - col_idx - 1, cur_eta_col))
        pivot_matrix, pivot_list = LUFactorization.generate_p(matrix)
        return (pivot_matrix, pivot_list), LUFactorization.lu_factorization(np.matmul(pivot_matrix, matrix))
