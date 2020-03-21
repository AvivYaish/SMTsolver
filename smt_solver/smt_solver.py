from formula_parser.formula_parser import FormulaParser
from smt_solver.congruence_graph import CongruenceGraph
from collections import deque
from copy import deepcopy


class SMTSolver:
    def __init__(self, formula, max_new_clauses=float('inf'), halving_period=10000):
        (self._formula, (self._tseitin_variable_to_subterm, self._subterm_to_tseitin_variable),
         (self._non_boolean_clauses, self._basic_congruence_graph)) = FormulaParser.import_uf(formula)

        # TODO: should keep the basic congruence graph updated relative to the BCP at level 0, can save time
        self._max_new_clauses = max_new_clauses
        self._halving_period = halving_period

    def _congruence_closure(self, assignment):
        positive_relations = deque()
        negative_relations = []
        for variable in assignment:
            subterm = self._tseitin_variable_to_subterm[variable]
            if subterm in self._non_boolean_clauses:    # If the variable represents an equality
                if assignment[variable]:
                    positive_relations.append(subterm)
                else:
                    negative_relations.append(subterm)

        graph = deepcopy(self._basic_congruence_graph)
        all_positive_relations = graph.process_positive_relations(positive_relations)
        conflict = graph.process_negative_relations(negative_relations)
        if conflict is None:
            return None
        return all_positive_relations | {conflict}
