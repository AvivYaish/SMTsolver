from formula_parser.formula_parser import FormulaParser
from sat_solver.sat_solver import SATSolver
from copy import deepcopy


class SMTSolver:
    def __init__(self, formula, max_new_clauses=float('inf'), halving_period=10000):
        (cnf_formula, (self._tseitin_variable_to_subterm, self._subterm_to_tseitin_variable),
         (self._non_boolean_clauses, self._basic_congruence_graph)) = FormulaParser.import_uf(formula)

        # TODO: should keep the basic congruence graph updated relative to the BCP at level 0, can save time
        self._solver = SATSolver(cnf_formula, max_new_clauses=max_new_clauses, halving_period=halving_period)

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

        # TODO: should only deepcopy if the SATSolver did a backjump since last time
        # TODO: maybe keep a graph for each level, and when backjump erase all unnecessary levels
        graph = deepcopy(self._basic_congruence_graph)
        graph.process_positive_relations(positive_relations)
        conflict = graph.process_negative_relations(negative_relations)
        if conflict is None:
            return None
        return frozenset({-self._subterm_to_tseitin_variable[subterm] for subterm in positive_relations}
                         | {self._subterm_to_tseitin_variable[conflict]})
