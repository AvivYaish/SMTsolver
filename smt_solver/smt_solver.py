from sat_solver.sat_solver import SATSolver
from copy import deepcopy


class SMTSolver:
    def __init__(self, cnf_formula, tseitin_mappings, theory_datastructures,
                 max_new_clauses=float('inf'), halving_period=10000):
        self._tseitin_variable_to_subterm, self._subterm_to_tseitin_variable = tseitin_mappings
        self._non_boolean_clauses, self._basic_congruence_graph = theory_datastructures

        self._congruence_graph_by_level = []
        self._solver = SATSolver(cnf_formula, max_new_clauses=max_new_clauses, halving_period=halving_period)

    def create_new_decision_level(self):
        if len(self._congruence_graph_by_level) == 0:
            graph_to_append = deepcopy(self._basic_congruence_graph)
        else:
            graph_to_append = deepcopy(self._congruence_graph_by_level[-1])
        self._congruence_graph_by_level.append(graph_to_append)

    def backtrack(self, level: int):
        while len(self._congruence_graph_by_level) > level + 1:
            self._congruence_graph_by_level.pop()

    def _congruence_closure(self):
        assignment = self._solver.get_assignment()
        positive_relations = []
        negative_relations = []
        for variable in assignment:
            subterm = self._tseitin_variable_to_subterm[variable]
            if subterm in self._non_boolean_clauses:    # If the variable represents an equality
                if assignment[variable]:
                    positive_relations.append(subterm)
                else:
                    negative_relations.append(subterm)

        graph = self._congruence_graph_by_level[-1]
        graph.process_positive_relations(positive_relations)
        conflict = graph.process_negative_relations(negative_relations)
        if conflict is None:
            return None
        return frozenset({-self._subterm_to_tseitin_variable[subterm] for subterm in positive_relations}
                         | {self._subterm_to_tseitin_variable[conflict]})
