class SMTSolver:

    def __init__(self, cnf_formula=None, max_new_clauses=float('inf'), halving_period=10000):
        """
        :param cnf_formula: a formula, in CNF. A formula is a set of clauses, where each clause is a frozenset.
        """
        if cnf_formula is None:
            cnf_formula = frozenset()

        self._formula = cnf_formula
        self._max_new_clauses = max_new_clauses
        self._halving_period = halving_period


