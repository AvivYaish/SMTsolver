from collections import deque
from itertools import product


class CongruenceGraph:
    @staticmethod
    def _replace_parameter(term, parameter_to_replace, new_parameter):
        new_term = list(term)
        for idx, parameter in enumerate(new_term):
            if (idx > 0) and (parameter == parameter_to_replace):
                new_term[idx] = new_parameter
        return tuple(new_term)

    def __init__(self, signature, parsed_formulas, all_ops, all_binary_ops):
        self._graph = {}
        formula_list = deque(parsed_formulas)
        while formula_list:
            cur_formula = formula_list.popleft()
            if (not cur_formula) or (cur_formula in self._graph):
                continue

            operator = cur_formula[0]
            if operator not in all_ops:
                # Base cases: 1. A constant, 2. Only one variable, 3. A function
                if operator in signature:  # A function
                    new_parameters = False
                    for parameter in cur_formula[1:]:
                        if parameter in self._graph:
                            self._graph[parameter]["parents"][cur_formula] = cur_formula
                        else:
                            formula_list.append(parameter)
                            new_parameters = True
                    if new_parameters:
                        formula_list.append(cur_formula)
                        continue
                self._graph[cur_formula] = {"parents": {}, "find": cur_formula}
            else:
                formula_list.append(cur_formula[1])
                if operator in all_binary_ops:
                    formula_list.append(cur_formula[2])

    def _find_representative(self, term):
        prev_term = None
        while term != prev_term:
            prev_term = term
            term = self._graph[term]["find"]
        return term

    def process_positive_relations(self, relations):
        all_positive_relations = set()
        while relations:
            op, term1, term2 = relations.popleft()
            all_positive_relations.add((op, term1, term2))
            rep1, rep2 = self._find_representative(term1), self._find_representative(term2)

            # Update the representation of parents of rep1
            for parent1, replaced_parent1 in self._graph[rep1]["parents"].items():
                self._graph[rep1]["parents"][parent1] = CongruenceGraph._replace_parameter(replaced_parent1, rep1, rep2)

            # Add congruent parents
            for parent1, parent2 in product(self._graph[rep1]["parents"], self._graph[rep2]["parents"]):
                replaced_parent1 = self._graph[rep1]["parents"][parent1]
                replaced_parent2 = self._graph[rep2]["parents"][parent2]
                if replaced_parent1 == replaced_parent2:
                    relations.appendleft((op, parent1, parent2))

            self._graph[rep1]["find"] = rep2
            # Update parents
            for parent1, replaced_parent1 in self._graph[rep1]["parents"].items():
                self._graph[rep2]["parents"][parent1] = replaced_parent1
            self._graph[rep1]["parents"] = {}
        return all_positive_relations

    def process_negative_relations(self, relations):
        while relations:
            op, term1, term2 = relations.pop()
            if self._find_representative(term1) == self._find_representative(term2):
                return op, term1, term2
        return None
