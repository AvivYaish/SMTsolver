from smt_solver.solver.solver import Solver
from smt_solver.sat_solver.sat_solver import SATSolver


class TheorySolver(Solver):
    def __init__(self, formula, tseitin_variable_to_subterm, non_boolean_clauses,
                 max_new_clauses=float('inf'), halving_period=10000):
        super().__init__()
        self._formula, self._tseitin_variable_to_subterm, self._non_boolean_clauses = \
            formula, tseitin_variable_to_subterm, non_boolean_clauses
        self._solver = SATSolver(formula,
                                 max_new_clauses=max_new_clauses,
                                 halving_period=halving_period,
                                 theory_solver=self)

    def get_assignment(self):
        assignment = {}
        for variable, value in self._solver.iterable_assignment():
            if variable in self._tseitin_variable_to_subterm:
                assignment[self._tseitin_variable_to_subterm[variable]] = value
        return assignment

    def solve(self) -> bool:
        return self._solver.solve()
