from smt_solver.formula_parser.formula_parser import FormulaParser
from smt_solver.solver.theory_solver import TheorySolver
from copy import deepcopy


class UFSolver(TheorySolver):
    def __init__(self, formula, tseitin_mappings, theory_data_structures, max_new_clauses=float('inf'),
                 halving_period=10000):
        tseitin_variable_to_subterm, self._subterm_to_tseitin_variable = tseitin_mappings
        non_boolean_clauses, self._basic_congruence_graph = theory_data_structures
        super().__init__(formula, tseitin_variable_to_subterm, non_boolean_clauses, max_new_clauses, halving_period)
        self._congruence_graph_by_level = []

    def create_new_decision_level(self):
        if len(self._congruence_graph_by_level) == 0:
            graph_to_append = deepcopy(self._basic_congruence_graph)
        else:
            graph_to_append = deepcopy(self._congruence_graph_by_level[-1])
        self._congruence_graph_by_level.append(graph_to_append)

    def backtrack(self, level: int):
        while len(self._congruence_graph_by_level) > level + 1:
            self._congruence_graph_by_level.pop()

    def _create_new_assignments(self, new_relations):
        new_assigments = []
        for new_relation in new_relations:
            # propagate new equalities from new_relations
            if new_relation not in self._subterm_to_tseitin_variable:
                new_relation = FormulaParser.symmetric_formula(new_relation)
                if new_relation not in self._subterm_to_tseitin_variable:
                    continue
            new_assigments.append(self._subterm_to_tseitin_variable[new_relation])
        return new_assigments

    def propagate(self):
        positive_relations, negative_relations = set(), []
        if self._non_boolean_clauses:
            for variable, value in self._solver.iterable_assignment():
                # Under the assumption that all literals are equations, this is faster than going over all equations
                if variable in self._tseitin_variable_to_subterm:
                    subterm = self._tseitin_variable_to_subterm[variable]
                    if subterm in self._non_boolean_clauses:    # If the variable represents an equality
                        if value:
                            positive_relations.add(subterm)
                        else:
                            negative_relations.append(subterm)

        graph = self._congruence_graph_by_level[-1]
        new_positive_relations = graph.process_positive_relations(positive_relations)
        conflict = graph.process_negative_relations(negative_relations)
        if conflict is None:
            return None, self._create_new_assignments(new_positive_relations)
        return frozenset({-self._subterm_to_tseitin_variable[subterm] for subterm in positive_relations}
                         | {self._subterm_to_tseitin_variable[conflict]}), None
