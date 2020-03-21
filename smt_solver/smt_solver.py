from formula_parser.formula_parser import FormulaParser
from collections import deque
from itertools import product


class SMTSolver:
    def __init__(self, formula, max_new_clauses=float('inf'), halving_period=10000):
        (self._formula, (self._tseitin_variable_to_subterm, self._subterm_to_tseitin_variable),
         (self._non_boolean_clauses, self._congruence_graph)) = FormulaParser.import_uf(formula)

        self._max_new_clauses = max_new_clauses
        self._halving_period = halving_period

    def _find_representative(self, term):
        prev_term = None
        while term != prev_term:
            prev_term = term
            term = self._congruence_graph[term]["find"]
        return term

    def _congruence_closure(self, assignment) -> bool:
        equalities = deque()
        nequalities = []
        for variable in assignment:
            subterm = self._tseitin_variable_to_subterm[variable]
            if subterm in self._non_boolean_clauses:
                # If the variable represents an equality
                if assignment[variable]:
                    equalities.append(subterm)
                else:
                    nequalities.append(subterm)

        while equalities:
            equality = equalities.popleft()
            term1, term2 = equality[1], equality[2]
            rep1, rep2 = self._find_representative(term1), self._find_representative(term2)

            new_parents = set()
            for parent1 in self._congruence_graph[rep1]["parents"]:
                new_parents.append(FormulaParser.replace_parameter(parent1, rep1, rep2))
            self._congruence_graph[rep1]["parents"] = set()

            for parent1, parent2 in product(new_parents, self._congruence_graph[rep2]["parents"]):
                self._congruence_graph[rep2]["parents"].add(parent1)
                if parent1 == parent2:
                    equalities.append(parent1)

        while nequalities:
            nequality = nequalities.pop()
            term1, term2 = nequality[1], nequality[2]
            if self._find_representative(term1) == self._find_representative(term2):
                return False
        return True
