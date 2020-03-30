from collections import deque, Counter


class SATSolver:

    def __init__(self,
                 cnf_formula=None,
                 max_new_clauses=float('inf'),
                 halving_period=10000,
                 theory_solver=None):
        """
        :param cnf_formula: a formula, in CNF. A formula is a set of clauses, where each clause is a frozenset.
        """
        if cnf_formula is None:
            cnf_formula = frozenset()

        self._formula = cnf_formula
        self._max_new_clauses = max_new_clauses
        self._halving_period = halving_period  # The time period after which all VSIDS counters are halved
        self._theory_solver = theory_solver

        self._new_clauses = deque()
        self._assignment = dict()
        self._assignment_by_level = []
        self._satisfaction_by_level = []
        self._literal_to_clause = {}
        self._satisfied_clauses = set()
        self._last_assigned_literals = deque()      # a queue of the literals assigned in the last level
        self._literal_to_watched_clause = {}        # A literal -> set(clause) dictionary.

        # VSIDS related fields
        self._unassigned_vsids_count = Counter()
        self._assigned_vsids_count = {}
        self._step_counter = 0                      # Counts how many decisions have been made

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

    def _unassign(self, variable: int):
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
        return {var: val for var, val in self.iterable_assignment()}

    def get_variable_assignment(self, variable):
        return self._assignment.get(variable, {"value": None})["value"]

    def iterable_assignment(self):
        """
        :return: a (variable, value) tuple for every assigned variable.
        """
        for var in self._assignment:
            yield var, self._assignment[var]["value"]

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

            clause_on_incoming_edge = self._assignment[abs(last_literal)]["clause"]
            if (max_level_count == 1) or (clause_on_incoming_edge is None):
                # If the last assigned literal is the only one from the last decision level,
                # or if it was assigned because of the theory (thus, the incoming clause is None):
                # return the conflict clause, the next literal to assign (which should be the
                # watch literal of the conflict clause), and the decision level to jump to
                if (prev_max_level == -1) and (max_level != -1):
                    prev_max_level = max_level - 1
                return frozenset(conflict_clause), last_literal, prev_max_level

            # Resolve the conflict clause with the clause on the incoming edge
            # Might be the case that the last literal was assigned because of the
            # theory, and in that case it is impossible to do resolution
            conflict_clause |= clause_on_incoming_edge
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
        if self._theory_solver:
            self._theory_solver.backtrack(level)

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
        if self._theory_solver:
            self._theory_solver.create_new_decision_level()

    def _satisfy_unit_clauses(self):
        self._create_new_decision_level()
        for clause in self._formula:
            if len(clause) == 1:
                for literal in clause:
                    if abs(literal) not in self._assignment:
                        self._assign(clause, literal)

    def _theory_propagation_to_exhaustion(self):
        if self._theory_solver is None:
            return True
        conflict_clause, new_assignments = self._theory_solver.congruence_closure()
        while conflict_clause is not None:
            cur_level = len(self._assignment_by_level) - 1
            if cur_level == 0:
                return False
            decision_literal = self._assignment_by_level[cur_level][0]
            if not self._assignment[abs(decision_literal)]["value"]:
                decision_literal = -decision_literal
            self._backtrack(cur_level - 1)
            self._add_conflict_clause(conflict_clause)
            if len(conflict_clause) == 1:
                for literal in conflict_clause:
                    self._assign(conflict_clause, literal)
            else:
                self._assign(None, -decision_literal)
            conflict_clause, new_assignments = self._theory_solver.congruence_closure()

        for literal in new_assignments:
            self._assign(None, literal)
        return True

    def _propagation(self) -> bool:
        while self._last_assigned_literals:
            if (not self._bcp_to_exhaustion()) or (not self._theory_propagation_to_exhaustion()):
                return False
        return True

    def _is_sat(self) -> bool:
        return self._formula.issubset(self._satisfied_clauses)

    def solve(self) -> bool:
        """
        :return: True if SAT, False otherwise.
        """
        self._satisfy_unit_clauses()
        while True:
            self._increment_step()
            if not self._propagation():
                return False
            if self._is_sat():
                return True
            self._decide()
