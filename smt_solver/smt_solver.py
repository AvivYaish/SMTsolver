from smt_solver.solver.solver import Solver


class SMTSolver(Solver):
    def __init__(self, formula=None, max_new_clauses=float('inf'), halving_period=10000):
        pass

    def get_assignment(self):
        pass

    def solve(self) -> bool:
        pass
