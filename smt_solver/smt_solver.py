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

    def _process_equalities(self, equalities):
        while equalities:
            term1, term2 = equalities.popleft()
            rep1, rep2 = self._find_representative(term1), self._find_representative(term2)

            # Update the representation of parents of rep1
            for parent1, replaced_parent1 in self._congruence_graph[rep1]["parents"].items():
                self._congruence_graph[rep1]["parents"][parent1] = \
                    FormulaParser.replace_parameter(replaced_parent1, rep1, rep2)

            # Add congruent parents
            for parent1, parent2 in product(self._congruence_graph[rep1]["parents"],
                                            self._congruence_graph[rep2]["parents"]):
                replaced_parent1 = self._congruence_graph[rep1]["parents"][parent1]
                replaced_parent2 = self._congruence_graph[rep2]["parents"][parent2]
                if replaced_parent1 == replaced_parent2:
                    equalities.appendleft((parent1, parent2))

            self._congruence_graph[rep1]["find"] = rep2
            # Update parents
            for parent1, replaced_parent1 in self._congruence_graph[rep1]["parents"].items():
                self._congruence_graph[rep2]["parents"][parent1] = replaced_parent1
            self._congruence_graph[rep1]["parents"] = {}

    def _process_inequalities(self, inequalities) -> bool:
        while inequalities:
            term1, term2 = inequalities.pop()
            if self._find_representative(term1) == self._find_representative(term2):
                return False
        return True

    def _congruence_closure(self, assignment) -> bool:
        equalities = deque()
        inequalities = []
        for variable in assignment:
            subterm = self._tseitin_variable_to_subterm[variable]
            if subterm in self._non_boolean_clauses:
                # If the variable represents an equality
                if assignment[variable]:
                    equalities.append((subterm[1], subterm[2]))
                else:
                    inequalities.append((subterm[1], subterm[2]))

        self._process_equalities(equalities)
        return self._process_inequalities(inequalities)
