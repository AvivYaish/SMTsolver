from formula_parser.formula_parser import FormulaParser


class SMTSolver:
    def __init__(self, formula, max_new_clauses=float('inf'), halving_period=10000):
        (self._formula, (self._tseitin_variable_to_subterm, self._subterm_to_tseitin_variable),
         (self._non_boolean_clauses, self._congruence_graph)) = FormulaParser.import_uf(formula)

        self._max_new_clauses = max_new_clauses
        self._halving_period = halving_period

    def _process_equality(self, equality):
        pass

    def _congruence_closure(self):
        pass
