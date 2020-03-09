from collections import deque, Counter


class SATSolver:
    @staticmethod
    def import_file(filename):
        variables = {}
        with open(filename, 'r') as f:
            contents = f.read()

            # TODO: shouldn't pass line by line, there can be multi-line expressions
            for line in contents:
                tokens = line[1:-1].split()
                if tokens[0] == "declare-const":
                    variables[tokens[1]] = tokens[2]
                if tokens[0] == "assert":
                    pass
        return None

    @staticmethod
    def _find_closing_bracket(text: str) -> int:
        """
        Examples:

        :return: the index of t
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
        if formula and (formula[0] == "(") and (SATSolver._find_closing_bracket(formula) == len(formula)):
            return formula[1:-1].strip()
        return formula

    @staticmethod
    def _tseitin_tranform(formula: str):
        # TODO: this both parses and does the transform, should split to 2 functions
        # TODO: if there is not not, should erase both nots
        # TODO: if there is and formula1 formula1, should replace with formula1
        # TODO: same for or
        formula_list = [formula]
        subformulas = {}
        transformed_subformulas = {}
        transformed_formula = set()
        while formula_list:
            cur_formula = SATSolver._prepare_formula(formula_list.pop())
            if not cur_formula:
                continue

            if cur_formula not in subformulas:
                # + 1 to avoid getting zeros (-0=0)
                subformulas[cur_formula] = len(subformulas) + 1

            split_cur_formula = cur_formula.split(None, 1)

            # Base case, only one variable
            if len(split_cur_formula) == 1:
                continue

            operator = split_cur_formula[0]
            right_side = split_cur_formula[1]
            if operator not in {"not", "and", "or", "=>", "<=>"}:
                continue

            right_side = SATSolver._prepare_formula(right_side)
            if operator == "not":
                if right_side not in subformulas:
                    subformulas[right_side] = len(subformulas) + 1

                transformed_subformulas[subformulas[cur_formula]] = {
                    frozenset({-subformulas[cur_formula], -subformulas[right_side]}),
                    frozenset({subformulas[cur_formula], subformulas[right_side]})
                }

                transformed_formula = transformed_formula.union(transformed_subformulas[subformulas[cur_formula]])
                formula_list.append(right_side)
                continue

            # Boolean operator
            if right_side and (right_side[0] == "("):
                closing_idx = SATSolver._find_closing_bracket(right_side)
                left_side = SATSolver._prepare_formula(right_side[:closing_idx])
                right_side = SATSolver._prepare_formula(right_side[closing_idx:])
            else:
                left_side, right_side = right_side.split()
            # TODO: Note, this creates redundant variables for
            #  things like (and (not (r)) (not r)): we'll get
            #  a variable for not (r) and not r,
            #  because we're looking at the actual text
            formula_list.append(left_side)
            formula_list.append(right_side)

            if left_side not in subformulas:
                subformulas[left_side] = len(subformulas) + 1
            if right_side not in subformulas:
                subformulas[right_side] = len(subformulas) + 1

            if operator == "and":
                transformed_subformulas[subformulas[cur_formula]] = {
                    frozenset({-subformulas[cur_formula], subformulas[left_side]}),
                    frozenset({-subformulas[cur_formula], subformulas[right_side]}),
                    frozenset({-subformulas[left_side], -subformulas[right_side], subformulas[cur_formula]}),
                }
            elif operator == "or":
                transformed_subformulas[subformulas[cur_formula]] = {
                    frozenset({-subformulas[cur_formula], subformulas[left_side], subformulas[right_side]}),
                    frozenset({-subformulas[left_side], subformulas[cur_formula]}),
                    frozenset({-subformulas[right_side], subformulas[cur_formula]})
                }
            elif operator == "=>":
                transformed_subformulas[subformulas[cur_formula]] = {
                    frozenset({-subformulas[cur_formula], -subformulas[left_side], subformulas[right_side]}),
                    frozenset({subformulas[left_side], subformulas[cur_formula]}),
                    frozenset({-subformulas[right_side], subformulas[cur_formula]})
                }
            elif operator == "<=>":
                # TODO: add tests for this
                transformed_subformulas[subformulas[cur_formula]] = {
                    # =>
                    frozenset({-subformulas[cur_formula], -subformulas[left_side], subformulas[right_side]}),
                    frozenset({subformulas[left_side], subformulas[cur_formula]}),
                    frozenset({-subformulas[right_side], subformulas[cur_formula]}),
                    # <=
                    frozenset({subformulas[cur_formula], subformulas[left_side], subformulas[right_side]}),
                    frozenset({subformulas[cur_formula], -subformulas[left_side], -subformulas[right_side]})
                }
            transformed_formula = transformed_formula.union(transformed_subformulas[subformulas[cur_formula]])
        return subformulas, transformed_subformulas, transformed_formula

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

    def __init__(self, formula=None, max_new_clauses=float('inf'), halving_period=100):
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
        self._decision_counter = 0             # Count how many decisions have been made
        self._halving_period = halving_period  # The time period after which all VSIDS counters are halved

        for clause in self._formula:
            self._add_clause(clause)

    def _add_clause(self, clause):
        for idx, literal in enumerate(clause):
            if literal not in self._literal_to_clause:
                self._literal_to_clause[literal] = set()
                self._literal_to_watched_clause[literal] = set()
            if (literal not in self._unassigned_vsids_count) and (literal not in self._assigned_vsids_count):
                self._unassigned_vsids_count[literal] = 0

            self._literal_to_clause[literal].add(clause)
            if idx <= 1:
                self._literal_to_watched_clause[literal].add(clause)
            if literal in self._unassigned_vsids_count:
                self._unassigned_vsids_count[literal] += 1
            elif literal in self._assigned_vsids_count:
                self._assigned_vsids_count[literal] += 1

    def _assign(self, clause, literal: int):
        variable = abs(literal)
        self._assignment[variable] = {
            "value": literal > 0,   # True or False
            "clause": clause,       # The clause which caused the assignment
            "level": len(self._assignment_by_level) - 1,
            "idx": len(self._assignment_by_level[-1])   # Defines an assignment order in the same level
        }

        # Keep data structures related to satisfied clauses up to date
        newly_satisfied_clauses = self._literal_to_clause[literal] - self._satisfied_clauses
        self._satisfaction_by_level[-1].extend(newly_satisfied_clauses)
        self._satisfied_clauses |= newly_satisfied_clauses

        # Keep data structures related to variable assignment up to date
        self._assignment_by_level[-1].append(variable)
        for cur_sign in [variable, -variable]:
            if cur_sign in self._literal_to_clause:
                self._last_assigned_literals.append(cur_sign)
                self._assigned_vsids_count[cur_sign] = self._unassigned_vsids_count[cur_sign]
                del self._unassigned_vsids_count[cur_sign]

    def _unassign(self, variable):
        del self._assignment[variable]
        for cur_sign in [variable, -variable]:
            if cur_sign in self._literal_to_clause:
                self._unassigned_vsids_count[cur_sign] = self._assigned_vsids_count[cur_sign]
                del self._assigned_vsids_count[cur_sign]

    def get_assignment(self):
        return {variable: self._assignment[variable]["value"] for variable in self._assignment}

    def _conflict_resolution(self, conflict_clause):
        conflict_clause = set(conflict_clause)
        while True:
            last_literal, prev_max_level, max_level, max_idx, max_count = None, -1, -1, -1, 0
            for literal in conflict_clause:
                variable = abs(literal)
                level, idx = self._assignment[variable]["level"], self._assignment[variable]["idx"]
                if level > max_level:
                    prev_max_level = max_level
                    max_level, max_idx, max_count = level, -1, 0
                elif level > prev_max_level:
                    prev_max_level = level
                if level == max_level:
                    max_count += 1
                    if idx > max_idx:
                        last_literal, max_idx = literal, idx

            if max_count == 1:
                # The last assigned literal is the only one from the last decision level
                # Return the conflict clause, the next literal to assign (which should be the watch literal of the
                # conflict clause), and the decision level to jump to
                return frozenset(conflict_clause), last_literal, prev_max_level

            # Resolve the conflict clause with the clause on the incoming edge
            conflict_clause |= self._assignment[abs(last_literal)]["clause"]
            conflict_clause.remove(last_literal)
            conflict_clause.remove(-last_literal)

    def _bcp(self):
        while self._last_assigned_literals:
            watch_literal = self._last_assigned_literals.popleft()
            for clause in (self._literal_to_watched_clause[watch_literal] - self._satisfied_clauses):
                conflict_clause = self._replace_watch_literal(clause, watch_literal)
                if conflict_clause is not None:
                    return conflict_clause
        return None # No conflict-clause

    def _replace_watch_literal(self, clause, watch_literal: int):
        """
        - If the clause is satisfied, nothing to do.
        - Else, it is not satisfied yet:
          - If it has 0 unassigned literals, it is UNSAT.
          - If it has 1 unassigned literals, assign the correct value to the last literal.
          - If it has > 2 unassigned literals, pick one to become the new watch literal.
        """
        unassigned_literals = []
        for unassigned_literal in clause:
            variable = abs(unassigned_literal)
            if variable in self._assignment:
                # If the current literal is assigned, it cannot replace the current watch literal
                continue
            unassigned_literals.append(unassigned_literal)

            if (len(unassigned_literals) > 1) and (clause not in self._literal_to_watched_clause[-watch_literal]):
                # The second condition implies we replaced the watch_literal and can stop searching for one.
                break

            if clause not in self._literal_to_watched_clause[unassigned_literal]:
                # If the current literal is already watching the clause, it cannot replace the watch literal
                self._literal_to_watched_clause[watch_literal].remove(clause)
                self._literal_to_watched_clause[unassigned_literal].add(clause)

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

    def _add_conflict_clause(self, conflict_clause, literal_to_assign: int):
        if self._max_new_clauses <= 0:
            return

        # Remove previous conflict clauses, if there are too many
        if len(self._new_clauses) == self._max_new_clauses:
            clause_to_remove = self._new_clauses.popleft()
            for literal in clause_to_remove:
                if literal in self._literal_to_watched_clause:
                    self._literal_to_watched_clause[literal].discard(clause_to_remove)

        self._new_clauses.append(conflict_clause)
        self._add_clause(conflict_clause)
        self._assign(conflict_clause, literal_to_assign)

    def _backtrack(self, level: int):
        self._last_assigned_literals = deque()
        while len(self._assignment_by_level) > level + 1:
            for variable in self._assignment_by_level.pop():
                self._unassign(variable)
            for clause in self._satisfaction_by_level.pop():
                self._satisfied_clauses.remove(clause)

    def _decide(self):
        # Maintain data structures related to VSIDS
        self._decision_counter += 1
        if self._decision_counter >= self._halving_period:
            for literal in self._unassigned_vsids_count:
                self._unassigned_vsids_count[literal] /= 2
            for literal in self._assigned_vsids_count:
                self._assigned_vsids_count[literal] /= 2

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
            conflict_clause = self._bcp()
            while conflict_clause is not None:
                conflict_clause, watch_literal, level_to_jump_to = self._conflict_resolution(conflict_clause)
                if level_to_jump_to == -1:
                    # An assignment that satisfies the formula's unit clauses causes a conflict, so the formula is UNSAT
                    return False
                self._backtrack(level_to_jump_to)
                self._add_conflict_clause(conflict_clause, watch_literal)
                conflict_clause = self._bcp()

            # If all clauses are satisfied, we are done
            if self._formula.issubset(self._satisfied_clauses):
                return True

            self._decide()
