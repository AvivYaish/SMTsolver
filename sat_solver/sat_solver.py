from collections import deque, Counter
import re


class SATSolver:
    @staticmethod
    def _find_closing_bracket(text: str) -> int:
        """
        :return: the index of the ')' bracket that closes the very first (left-most) '(' bracket.
        """
        flag = False
        counter = 0
        for idx, char in enumerate(text):
            if char == "(":
                flag = True
                counter += 1
            elif char == ")":
                counter -= 1
            if flag and (counter == 0):
                return idx + 1
        return -1

    @staticmethod
    def _prepare_formula(formula: str) -> str:
        """
        Prepares a string formula for parsing:
        1. "Unifies" all adjacent whitespace to a single space.
        2. Strips leading and trailing whitespace.
        3. Removes leading and trailing brackets.
        :param formula: a string representation of a formula, in SMT-LIBv2 language.
        :return: a "cleaned" up formula, ready for parsing.
        """
        formula = ' '.join(formula.split()).strip()
        while formula and (formula[0] == "(") and (SATSolver._find_closing_bracket(formula) == len(formula)):
            formula = formula[1:-1].strip()
        return formula

    _DECLARATION = re.compile(r'(\(\s*(declare-fun)\s+(\w+)\s+\(([^\)]*)\)\s+(\w+)\s*\))')
    _ASSERTION = re.compile(r'(\(\s*(assert)\s(.+)\s*\))')

    @staticmethod
    def _parse_formula_uf(formula: str, signature=None, parsed_formulas=None):
        """
        asserts and declarations are line separated, and are enclosed by a single ( and ).
        """
        if signature is None:
            signature = {}
        if parsed_formulas is None:
            parsed_formulas = []

        for match in re.finditer(SATSolver._DECLARATION, formula):
            name = match.group(3)
            parameters = match.group(4)
            output = match.group(5)
            signature[name] = {
                "output_type": output,
                "parameter_types": parameters.split()
            }

        for match in re.finditer(SATSolver._ASSERTION, formula):
            partial_formula = match.group(3)
            parsed_formulas.append(' '.join(partial_formula.split()).strip())

        return signature, parsed_formulas

    @staticmethod
    def _parse_formula(formula: str, variables=None):
        """
        :return: given a textual representation of an SMT-LIBv2 formula, returns a tuple representation of it.
        """
        if variables is None:
            variables = set()
        cur_formula = SATSolver._prepare_formula(formula)
        if not cur_formula:
            return None

        split_cur_formula = cur_formula.split(None, 1)
        if len(split_cur_formula) == 1:
            # Base case, only one variable/booolean value
            variable = split_cur_formula.pop()
            truth_value = variable.lower()
            if (truth_value != "true") and (truth_value != "false"):
                variables.add(truth_value)
            return variable

        right_side = split_cur_formula.pop()
        operator = split_cur_formula.pop().lower()
        if operator not in {"not", "and", "or", "=>", "<=>"}:
            raise ValueError('"' + operator + '" is not a supported operator.')

        if operator == "not":
            return operator, SATSolver._parse_formula(right_side, variables)

        # Boolean operator
        if right_side and (right_side[0] == "("):
            # If the first parameter of the operator is enclosed in brackets, split the first and second parameters
            # according to the location of the closing bracket.
            closing_idx = SATSolver._find_closing_bracket(right_side)
            left_side = SATSolver._prepare_formula(right_side[:closing_idx])
            right_side = SATSolver._prepare_formula(right_side[closing_idx:])
        else:
            left_side, right_side = right_side.split()
        return operator, SATSolver._parse_formula(left_side, variables), SATSolver._parse_formula(right_side, variables)

    @staticmethod
    def _is_parameter_not(parameter):
        return (len(parameter) > 1) and (parameter[0] == "not")

    @staticmethod
    def _is_left_not_right(left_parameter, right_parameter):
        return (
            # This case is: op (not x) (x)
            (SATSolver._is_parameter_not(right_parameter) and (right_parameter[1] == left_parameter))
            or
            # This case is: op (not x) (x)
            (SATSolver._is_parameter_not(left_parameter) and (left_parameter[1] == right_parameter))
        )

    @staticmethod
    def _simplify_formula(parsed_formula):
        # Base case, empty formula
        if (not parsed_formula) or (parsed_formula == ""):
            return "true"

        # Base case, only one variable/boolean value
        operator = parsed_formula[0]
        if operator not in {"not", "and", "or", "=>", "<=>"}:
            return parsed_formula

        left_parameter = SATSolver._simplify_formula(parsed_formula[1])
        if operator == "not":
            if SATSolver._is_parameter_not(left_parameter):
                # not (not x)
                return left_parameter[1]
            if left_parameter == "false":
                return "true"
            elif left_parameter == "true":
                return "false"
            return operator, left_parameter

        # Boolean operator
        right_parameter = SATSolver._simplify_formula(parsed_formula[2])
        if left_parameter == right_parameter:
            if (operator == "=>") or (operator == "<=>"):
                return "true"
            return left_parameter
        elif (operator == "or") or (operator == "and"):
            if operator == "or":
                first_bool, second_bool = "true", "false"
            else:
                first_bool, second_bool = "false", "true"
            if (
                    # Either: op (x) (first_bool), or: op (first_bool) (x)
                    (left_parameter == first_bool) or (right_parameter == first_bool)
                    or
                    # Either: op (x) (not x), or: op (not x) (x)
                    SATSolver._is_left_not_right(left_parameter, right_parameter)
            ):
                return first_bool
            if left_parameter == second_bool:
                return right_parameter
            if right_parameter == second_bool:
                return left_parameter
        elif operator == "=>":
            if (right_parameter == "true") or (left_parameter == "false"):
                return "true"
            if right_parameter == "false":
                return "not", left_parameter
            if (left_parameter == "true") or SATSolver._is_left_not_right(left_parameter, right_parameter):
                return right_parameter
        elif operator == "<=>":
            if left_parameter == "true":
                return right_parameter
            if right_parameter == "true":
                return left_parameter
            if left_parameter == "false":
                return "not", right_parameter
            if right_parameter == "false":
                return "not", left_parameter
            if SATSolver._is_left_not_right(left_parameter, right_parameter):
                return "false"
        return operator, left_parameter, right_parameter

    @staticmethod
    def _tseitin_transform(parsed_formula, output_all=False):
        formula_list = [parsed_formula]
        subformulas = {}
        transformed_subformulas = {}
        transformed_formula = set()
        while formula_list:
            cur_formula = formula_list.pop()
            if not cur_formula:
                continue

            if cur_formula not in subformulas:
                # + 1 to avoid getting zeros (-0=0)
                subformulas[cur_formula] = len(subformulas) + 1

            operator = cur_formula[0]
            if operator not in {"not", "and", "or", "=>", "<=>"}:
                continue

            left_parameter = cur_formula[1]
            if operator == "not":
                if left_parameter not in subformulas:
                    subformulas[left_parameter] = len(subformulas) + 1

                transformed_subformulas[subformulas[cur_formula]] = {
                    frozenset({-subformulas[cur_formula], -subformulas[left_parameter]}),
                    frozenset({subformulas[cur_formula], subformulas[left_parameter]})
                }

                transformed_formula = transformed_formula.union(transformed_subformulas[subformulas[cur_formula]])
                formula_list.append(left_parameter)
                continue

            # Boolean operator
            right_parameter = cur_formula[2]
            formula_list.append(left_parameter)
            formula_list.append(right_parameter)

            if left_parameter not in subformulas:
                subformulas[left_parameter] = len(subformulas) + 1
            if right_parameter not in subformulas:
                subformulas[right_parameter] = len(subformulas) + 1

            if operator == "and":
                transformed_subformulas[subformulas[cur_formula]] = {
                    frozenset({-subformulas[cur_formula], subformulas[left_parameter]}),
                    frozenset({-subformulas[cur_formula], subformulas[right_parameter]}),
                    frozenset({-subformulas[left_parameter], -subformulas[right_parameter], subformulas[cur_formula]}),
                }
            elif operator == "or":
                transformed_subformulas[subformulas[cur_formula]] = {
                    frozenset({-subformulas[cur_formula], subformulas[left_parameter], subformulas[right_parameter]}),
                    frozenset({-subformulas[left_parameter], subformulas[cur_formula]}),
                    frozenset({-subformulas[right_parameter], subformulas[cur_formula]})
                }
            elif operator == "=>":
                transformed_subformulas[subformulas[cur_formula]] = {
                    frozenset({-subformulas[cur_formula], -subformulas[left_parameter], subformulas[right_parameter]}),
                    frozenset({subformulas[left_parameter], subformulas[cur_formula]}),
                    frozenset({-subformulas[right_parameter], subformulas[cur_formula]})
                }
            elif operator == "<=>":
                transformed_subformulas[subformulas[cur_formula]] = {
                    frozenset({-subformulas[cur_formula], -subformulas[left_parameter], subformulas[right_parameter]}),
                    frozenset({-subformulas[cur_formula], subformulas[left_parameter], -subformulas[right_parameter]}),
                    frozenset({subformulas[cur_formula], subformulas[left_parameter], subformulas[right_parameter]}),
                    frozenset({subformulas[cur_formula], -subformulas[left_parameter], -subformulas[right_parameter]}),
                }
            transformed_formula = transformed_formula.union(transformed_subformulas[subformulas[cur_formula]])
        transformed_formula.add(frozenset({1}))  # Always need to satisfy the entire formula
        if output_all:
            return subformulas, transformed_subformulas, transformed_formula
        return transformed_formula

    @staticmethod
    def _preprocessing(cnf_formula):
        """
        :param cnf_formula: a formula, in CNF.
        :return: processed formula.
        """
        preprocessed_formula = []
        for clause in cnf_formula:
            trivial_clause = False
            for literal in clause:
                if -literal in clause:
                    # Remove trivial clauses
                    # If the same variable appears twice with
                    # different signs in the same clause
                    trivial_clause = True
                    break

            if trivial_clause or (len(clause) == 0):
                # Remove empty clauses
                continue

            preprocessed_formula.append(clause)
        return frozenset(preprocessed_formula)

    @staticmethod
    def convert_string_formula(formula: str):
        simplified_formula = SATSolver._simplify_formula(SATSolver._parse_formula(formula))
        if simplified_formula == "true":
            return frozenset({})
        elif simplified_formula == "false":
            return frozenset({frozenset({1}), frozenset({-1})})
        return SATSolver._tseitin_transform(simplified_formula)

    @staticmethod
    def convert_tseitin_assignment_to_regular(formula: str, assignment):
        variables = set()
        simplified_formula = SATSolver._simplify_formula(SATSolver._parse_formula(formula, variables))
        if simplified_formula == "true":
            return frozenset({})
        elif simplified_formula == "false":
            return frozenset({frozenset({1}), frozenset({-1})})
        subformulas, transformed_subformulas, transformed_formula = SATSolver._tseitin_transform(simplified_formula)
        # for variable in assignment:
        #     if subformulas[]

    def __init__(self, formula=None, max_new_clauses=float('inf'), halving_period=10000):
        """
        :param formula: a formula, in CNF. A formula is a set of clauses, where each clause is a frozenset.
        """
        if formula is None:
            formula = set()

        self._formula = SATSolver._preprocessing(formula)
        self._new_clauses = deque()
        self._max_new_clauses = max_new_clauses
        self._assignment = dict()
        self._assignment_by_level = []
        self._satisfaction_by_level = []
        self._literal_to_clause = {}
        self._satisfied_clauses = set()
        self._last_assigned_literals = deque()               # a queue of the literals assigned in the last level
        self._literal_to_watched_clause = {}                   # A literal -> set(clause) dictionary.

        # VSIDS related fields
        self._unassigned_vsids_count = Counter()
        self._assigned_vsids_count = {}
        self._step_counter = 0             # Count how many decisions have been made
        self._halving_period = halving_period  # The time period after which all VSIDS counters are halved

        for clause in self._formula:
            self._add_clause(clause)

    def _add_clause(self, clause):
        """
        Initialize all clause data structures for the given clause.
        """
        for idx, literal in enumerate(clause):
            variable = abs(literal)
            if literal not in self._literal_to_clause:
                self._literal_to_clause[literal] = set()
            if variable not in self._literal_to_watched_clause:
                self._literal_to_watched_clause[variable] = set()
            if (literal not in self._unassigned_vsids_count) and (literal not in self._assigned_vsids_count):
                self._unassigned_vsids_count[literal] = 0
                self._unassigned_vsids_count[-literal] = 0

            self._literal_to_clause[literal].add(clause)
            if idx <= 1:
                self._literal_to_watched_clause[variable].add(clause)
            if literal in self._unassigned_vsids_count:
                self._unassigned_vsids_count[literal] += 1
            elif literal in self._assigned_vsids_count:
                self._assigned_vsids_count[literal] += 1

    def _assign(self, clause, literal: int):
        """
        Assigns a satisfying value to the given literal.
        """
        variable = abs(literal)
        self._assignment[variable] = {
            "value": literal > 0,                           # Satisfy the literal
            "clause": clause,                               # The clause which caused the assignment
            "level": len(self._assignment_by_level) - 1,    # The decision level of the assignment
            "idx": len(self._assignment_by_level[-1])       # Defines an assignment order in the same level
        }

        # Keep data structures related to satisfied clauses up to date
        newly_satisfied_clauses = self._literal_to_clause[literal] - self._satisfied_clauses
        self._satisfaction_by_level[-1].extend(newly_satisfied_clauses)
        self._satisfied_clauses |= newly_satisfied_clauses

        # Keep data structures related to variable assignment up to date
        self._assignment_by_level[-1].append(variable)
        self._last_assigned_literals.append(literal)
        for cur_sign in [variable, -variable]:
            self._assigned_vsids_count[cur_sign] = self._unassigned_vsids_count[cur_sign]
            del self._unassigned_vsids_count[cur_sign]

    def _unassign(self, variable):
        """
        Unassigns the given variable.
        """
        del self._assignment[variable]
        for cur_sign in [variable, -variable]:
            self._unassigned_vsids_count[cur_sign] = self._assigned_vsids_count[cur_sign]
            del self._assigned_vsids_count[cur_sign]

    def get_assignment(self):
        """
        Returns the current assignment (variable-value pairs only).
        """
        return {variable: self._assignment[variable]["value"] for variable in self._assignment}

    def _conflict_resolution(self, conflict_clause):
        """
        Learns conflict clauses using implication graphs, with the Unique Implication Point heuristic.
        """
        conflict_clause = set(conflict_clause)
        while True:
            last_literal, prev_max_level, max_level, max_idx, max_level_count = None, -1, -1, -1, 0
            for literal in conflict_clause:
                variable = abs(literal)
                level, idx = self._assignment[variable]["level"], self._assignment[variable]["idx"]
                if level > max_level:
                    prev_max_level = max_level
                    last_literal, max_level, max_idx, max_level_count = literal, level, idx, 1
                elif level == max_level:
                    max_level_count += 1
                    if idx > max_idx:
                        last_literal, max_idx = literal, idx
                elif level > prev_max_level:
                    prev_max_level = level

            if max_level_count == 1:
                # The last assigned literal is the only one from the last decision level
                # Return the conflict clause, the next literal to assign (which should be the watch literal of the
                # conflict clause), and the decision level to jump to
                if (prev_max_level == -1) and (max_level != -1):
                    prev_max_level = max_level - 1
                return frozenset(conflict_clause), last_literal, prev_max_level

            # Resolve the conflict clause with the clause on the incoming edge
            conflict_clause |= self._assignment[abs(last_literal)]["clause"]
            conflict_clause.remove(last_literal)
            conflict_clause.remove(-last_literal)

    def _bcp(self):
        """
        Performs BCP, as triggered by the last assigned literals. If new literals are assigned as part of the BCP,
        the BCP continues using them. The BCP uses watch literals.
        :return: None, if there is no conflict. If there is one, the conflict clause is returned.
        """
        while self._last_assigned_literals:
            watch_literal = self._last_assigned_literals.popleft()
            for clause in self._literal_to_watched_clause[abs(watch_literal)].copy():
                if clause not in self._satisfied_clauses:
                    conflict_clause = self._replace_watch_literal(clause, watch_literal)
                    if conflict_clause is not None:
                        return conflict_clause
        return None  # No conflict-clause

    def _replace_watch_literal(self, clause, watch_literal: int):
        """
        - If the clause is satisfied, nothing to do.
        - Else, it is not satisfied yet:
          - If it has 0 unassigned literals, it is UNSAT.
          - If it has 1 unassigned literals, assign the correct value to the last literal.
          - If it has > 2 unassigned literals, pick one to become the new watch literal.
        """
        watch_variable = abs(watch_literal)
        replaced_watcher = False
        unassigned_literals = []
        for unassigned_literal in clause:
            unassigned_variable = abs(unassigned_literal)
            if unassigned_variable in self._assignment:
                # If the current literal is assigned, it cannot replace the current watch literal
                continue
            unassigned_literals.append(unassigned_literal)

            if replaced_watcher:
                # If we already replaced the watch_literal
                if len(unassigned_literals) > 1:
                    break
            elif clause not in self._literal_to_watched_clause[unassigned_variable]:
                # If the current literal is not already watching the clause, it can replace the watch literal
                self._literal_to_watched_clause[watch_variable].remove(clause)
                self._literal_to_watched_clause[unassigned_variable].add(clause)
                replaced_watcher = True

        if len(unassigned_literals) == 0:
            # Clause is UNSAT, return it as the conflict-clause
            return clause
        if len(unassigned_literals) == 1:
            # The clause is still not satisfied, and has only one unassigned literal.
            # Assign the correct value to it. Because it is now watching the clause,
            # and was also added to self._last_assigned_literals, we will later on
            # check if the assignment causes a conflict
            self._assign(clause, unassigned_literals.pop())
        return None

    def _add_conflict_clause(self, conflict_clause):
        """
        Adds a conflict clause to the formula.
        """
        if self._max_new_clauses <= 0:
            return

        # Remove previous conflict clauses, if there are too many
        if len(self._new_clauses) == self._max_new_clauses:
            clause_to_remove = self._new_clauses.popleft()
            for literal in clause_to_remove:
                self._literal_to_clause[literal].discard(clause_to_remove)
                self._literal_to_watched_clause[abs(literal)].discard(clause_to_remove)

        self._new_clauses.append(conflict_clause)
        self._add_clause(conflict_clause)

    def _bcp_to_exhaustion(self) -> bool:
        """
        :return: performs BCP until exhaustion, returns False iff formula is UNSAT.
        """
        conflict_clause = self._bcp()
        while conflict_clause is not None:
            conflict_clause, watch_literal, level_to_jump_to = self._conflict_resolution(conflict_clause)
            if level_to_jump_to == -1:
                # An assignment that satisfies the formula's unit clauses causes a conflict, so the formula is UNSAT
                return False
            self._backtrack(level_to_jump_to)
            self._add_conflict_clause(conflict_clause)
            self._assign(conflict_clause, watch_literal)
            conflict_clause = self._bcp()
        return True

    def _backtrack(self, level: int):
        """
        Non-chronological backtracking.
        """
        self._last_assigned_literals = deque()
        while len(self._assignment_by_level) > level + 1:
            for variable in self._assignment_by_level.pop():
                self._unassign(variable)
            for clause in self._satisfaction_by_level.pop():
                self._satisfied_clauses.remove(clause)

    def _increment_step(self):
        # Maintain data structures related to VSIDS
        self._step_counter += 1
        if self._step_counter >= self._halving_period:
            for literal in self._unassigned_vsids_count:
                self._unassigned_vsids_count[literal] /= 2
            for literal in self._assigned_vsids_count:
                self._assigned_vsids_count[literal] /= 2

    def _decide(self):
        """
        Decides which literal to assign next, using the VSIDS decision heuristic.
        """
        self._create_new_decision_level()
        literal, count = self._unassigned_vsids_count.most_common(1).pop()
        self._assign(None, literal)

    def _create_new_decision_level(self):
        self._assignment_by_level.append(list())
        self._satisfaction_by_level.append(list())

    def _satisfy_unit_clauses(self):
        self._create_new_decision_level()
        for clause in self._formula:
            if len(clause) == 1:
                for literal in clause:
                    if abs(literal) not in self._assignment:
                        self._assign(clause, literal)

    def solve(self) -> bool:
        """
        :return: True if SAT, False otherwise.
        """
        self._satisfy_unit_clauses()
        while True:
            # Iterative BCP
            self._increment_step()
            if not self._bcp_to_exhaustion():
                return False

            # If all clauses are satisfied, we are done
            if self._formula.issubset(self._satisfied_clauses):
                return True

            self._decide()
