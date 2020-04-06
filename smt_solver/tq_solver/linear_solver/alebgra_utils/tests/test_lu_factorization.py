from smt_solver.tq_solver.linear_solver.alebgra_utils.lu_factorization import LUFactorization
import numpy as np


class TestLUFactorization:
    MATRIX1 = np.array([[3, 1, 0], [1, 1, 0], [4, 3, 1]])

    @staticmethod
    def test_generate_p():
        matrix = TestLUFactorization.MATRIX1
        pivot_matrix, pivot_list = LUFactorization.generate_p(matrix)
        assert np.all(np.matmul(pivot_matrix, matrix) == np.array([[4, 3, 1], [3, 1, 0], [1, 1, 0]]))

    @staticmethod
    def test_pivoting():
        matrix = np.copy(TestLUFactorization.MATRIX1)
        pivot_matrix, pivot_list = LUFactorization.generate_p(matrix)
        assert np.all(LUFactorization.pivot_matrix(pivot_list, matrix) == np.array([[4, 3, 1], [3, 1, 0], [1, 1, 0]]))
        assert np.all(LUFactorization.pivot_matrix(pivot_list, matrix, reverse=True) == TestLUFactorization.MATRIX1)

    @staticmethod
    def test_decomposition():
        matrix = TestLUFactorization.MATRIX1
        pivot_matrix, pivot_list = LUFactorization.generate_p(matrix)
        pivoted_matrix = np.matmul(pivot_matrix, matrix)
        matrices = LUFactorization.lu_decomposition(pivoted_matrix)
        cur_matrix = np.identity(3)
        for cur_eta_matrix in matrices:
            cur_matrix = np.matmul(cur_matrix, cur_eta_matrix.get_full_matrix())
        assert np.all(pivoted_matrix == cur_matrix)
