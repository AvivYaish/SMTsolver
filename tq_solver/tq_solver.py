from sat_solver.sat_solver import SATSolver
from linear_solver.linear_solver import LinearSolver
import numpy as np


class TQSolver:
    def __init__(self, cnf_formula, tseitin_mappings, non_boolean_clauses,
                 max_new_clauses=float('inf'), halving_period=10000, epsilon=0.00000001):
        self._cnf_formula = cnf_formula
        self._tseitin_variable_to_subterm, self._subterm_to_tseitin_variable = tseitin_mappings
        self._non_boolean_clauses = non_boolean_clauses

        for clause in self._non_boolean_clauses:
            self._c = np.zeros(len(clause[1]), dtype=np.float64)
            break

        self._tseitin_variable_to_np = {}
        for clause in self._non_boolean_clauses:
            if clause in self._subterm_to_tseitin_variable:
                self._tseitin_variable_to_np[self._subterm_to_tseitin_variable[clause]] = {
                    True: (np.array(clause[1], dtype=np.float64), np.array(clause[2], dtype=np.float64)),
                    False: (-np.array(clause[1], dtype=np.float64), -np.array(clause[2] + epsilon, dtype=np.float64))
                }

        self._solver = SATSolver(cnf_formula,
                                 max_new_clauses=max_new_clauses,
                                 halving_period=halving_period,
                                 theory_solver=self)

    def create_new_decision_level(self):
        pass

    def backtrack(self, level: int):
        pass

    def propagate(self):
        conflict_clause, A, b = set(), [], []
        for variable, value in self._solver.iterable_assignment():
            # Under the assumption that all literals are inequalities, this is faster than going over all inequalities
            if variable in self._tseitin_variable_to_np:
                A.append(self._tseitin_variable_to_np[variable][value][0])
                b.append(self._tseitin_variable_to_np[variable][value][1])
                conflict_clause.add(-variable if value else variable)

        if (not A) or LinearSolver(np.array(A), np.array(b), self._c).is_sat():
            conflict_clause = None
        else:
            conflict_clause = frozenset(conflict_clause)
        return conflict_clause, []

    def get_assignment(self):
        assignment = {}
        for variable, value in self._solver.iterable_assignment():
            if variable in self._tseitin_variable_to_subterm:
                assignment[self._tseitin_variable_to_subterm[variable]] = value
        return assignment

    def solve(self) -> bool:
        return self._solver.solve()
