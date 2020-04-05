from smt_solver.solver.theory_solver import TheorySolver
from smt_solver.tq_solver.linear_solver.linear_solver import LinearSolver
import numpy as np


class TQSolver(TheorySolver):
    def __init__(self, formula, tseitin_mappings, non_boolean_clauses, epsilon=np.float64(1e-5),
                 max_new_clauses=float('inf'), halving_period=10000):
        """
        :param epsilon: defines the precision for solving equations that are ">", lower values are better.
        """
        tseitin_variable_to_subterm, subterm_to_tseitin_variable = tseitin_mappings
        super().__init__(formula, tseitin_variable_to_subterm, non_boolean_clauses, max_new_clauses, halving_period)

        for clause in self._non_boolean_clauses:
            self._c = np.zeros(len(clause[1]), dtype=np.float64)
            break

        self._tseitin_variable_to_np = {}
        for clause in self._non_boolean_clauses:
            self._tseitin_variable_to_np[subterm_to_tseitin_variable[clause]] = {
                True: (np.array(clause[1], dtype=np.float64), np.array(clause[2], dtype=np.float64)),
                False: (-np.array(clause[1], dtype=np.float64), -np.array(clause[2] + epsilon, dtype=np.float64))
            }

    def propagate(self):
        conflict_clause, a_matrix, b = set(), [], []
        for variable, value in self._solver.iterable_assignment():
            # Under the assumption that all literals are inequalities, this is faster than going over all inequalities
            if variable in self._tseitin_variable_to_np:
                a_matrix.append(self._tseitin_variable_to_np[variable][value][0])
                b.append(self._tseitin_variable_to_np[variable][value][1])
                conflict_clause.add(-variable if value else variable)

        if (not a_matrix) or LinearSolver(np.array(a_matrix), np.array(b), self._c).is_sat():
            conflict_clause = None
        else:
            conflict_clause = frozenset(conflict_clause)
        return conflict_clause, []
