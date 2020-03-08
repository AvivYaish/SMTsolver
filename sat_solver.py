from collections import deque, Counter


def find_closing_bracket(text: str) -> int:
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


def prepare_formula(formula: str) -> str:
    """
    Prepares a string formula for parsing:
    1. "Unifies" all adjacent whitespace to a single space.
    2. Strips leading and trailing whitespace.
    3. Removes leading and trailing brackets.
    Examples:
    >>> prepare_formula('         ')
    ''
    >>> prepare_formula('   and    a     b    ')
    'and a b'
    >>> prepare_formula('   (   and a b     )     ')
    'and a b'
    >>> prepare_formula('(and (a) (b))')
    'and (a) (b)'
    >>> prepare_formula('and (a) (b)')
    'and (a) (b)'
    :param formula: a string representation of a formula, in SMT-LIBv2 language.
    :return: a "cleaned" up formula, ready for parsing.
    """
    formula = ' '.join(formula.split()).strip()
    if formula and (formula[0] == "(") and (find_closing_bracket(formula) == len(formula)):
        return formula[1:-1].strip()
    return formula


def tseitin_tranform(formula: str):
    """
    Examples:
    >>> tseitin_tranform("not (=> (not (and p q)) (not r))")
    ({'not (=> (not (and p q)) (not r))': 1, '=> (not (and p q)) (not r)': 2, 'not (and p q)': 3, 'not r': 4, 'r': 5, \
'and p q': 6, 'p': 7, 'q': 8}, \
{1: {frozenset({-1, -2}), frozenset({1, 2})}, 2: {frozenset({2, -4}), frozenset({2, 3}), frozenset({4, -3, -2})}, \
4: {frozenset({-5, -4}), frozenset({4, 5})}, 3: {frozenset({-6, -3}), frozenset({3, 6})}, 6: {frozenset({8, -6}), \
frozenset({-8, -7, 6}), frozenset({-6, 7})}}, \
{frozenset({2, 3}), frozenset({1, 2}), frozenset({-8, -7, 6}), frozenset({4, 5}), frozenset({-6, -3}), \
frozenset({3, 6}), frozenset({4, -3, -2}), frozenset({-1, -2}), frozenset({8, -6}), frozenset({-5, -4}), \
frozenset({-6, 7}), frozenset({2, -4})})
    >>> tseitin_tranform("not (=> (not (and pq78 q)) (not r))")
    ({'not (=> (not (and pq78 q)) (not r))': 1, '=> (not (and pq78 q)) (not r)': 2, 'not (and pq78 q)': 3, 'not r': 4, \
'r': 5, 'and pq78 q': 6, 'pq78': 7, 'q': 8}, \
{1: {frozenset({-1, -2}), frozenset({1, 2})}, 2: {frozenset({2, -4}), frozenset({2, 3}), frozenset({4, -3, -2})}, \
4: {frozenset({-5, -4}), frozenset({4, 5})}, 3: {frozenset({-6, -3}), frozenset({3, 6})}, 6: {frozenset({8, -6}), \
frozenset({-8, -7, 6}), frozenset({-6, 7})}}, \
{frozenset({2, 3}), frozenset({1, 2}), frozenset({-8, -7, 6}), frozenset({4, 5}), frozenset({-6, -3}), \
frozenset({3, 6}), frozenset({4, -3, -2}), frozenset({-1, -2}), frozenset({8, -6}), frozenset({-5, -4}), \
frozenset({-6, 7}), frozenset({2, -4})})
    """
    # TODO: this both parses and does the transform, should split to 2 functions
    # TODO: if there is not not, should erase both nots
    # TODO: if there is and formula1 formula1, should replace with formula1
    # TODO: same for or
    formula_list = [formula]
    subformulas = {}
    transformed_subformulas = {}
    transformed_formula = set()
    while formula_list:
        cur_formula = prepare_formula(formula_list.pop())
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

        right_side = prepare_formula(right_side)
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
            closing_idx = find_closing_bracket(right_side)
            left_side = prepare_formula(right_side[:closing_idx])
            right_side = prepare_formula(right_side[closing_idx:])
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


def unit_propagation(clause, assignment, level):
    """
    >>> unit_propagation(frozenset({}), {}, 0)
    {}
    >>> unit_propagation(frozenset({1}), {}, 0)
    {1: {'value': True, 'clause': frozenset({1}), 'level': 0}}
    >>> unit_propagation(frozenset({-1}), {}, 0)
    {1: {'value': False, 'clause': frozenset({-1}), 'level': 0}}
    >>> unit_propagation(frozenset({-1}), {1: {'value': True, 'clause': frozenset({1}), 'level': 0}}, 0)
    {1: {'value': True, 'clause': frozenset({1}), 'level': 0}}
    >>> unit_propagation(frozenset({-1}), {1: {'value': False, 'clause': frozenset({1}), 'level': 0}}, 0)
    {1: {'value': False, 'clause': frozenset({1}), 'level': 0}}
    >>> unit_propagation(frozenset({-1}), {1: {'value': False, 'clause': frozenset({1}), 'level': 0}}, 1)
    {1: {'value': False, 'clause': frozenset({1}), 'level': 0}}
    >>> unit_propagation(frozenset({1, 2, 3, 4}),
    ... {1: {'value': False, 'clause': frozenset({1, 2, 3, 4}), 'level': 0},
    ... 2: {'value': False, 'clause': frozenset({1, 2, 3, 4}), 'level': 0},
    ... 3: {'value': False, 'clause': frozenset({1, 2, 3, 4}), 'level': 0}}, 0)
    {1: {'value': False, 'clause': frozenset({1, 2, 3, 4}), 'level': 0}, \
2: {'value': False, 'clause': frozenset({1, 2, 3, 4}), 'level': 0}, \
3: {'value': False, 'clause': frozenset({1, 2, 3, 4}), 'level': 0}, \
4: {'value': True, 'clause': frozenset({1, 2, 3, 4}), 'level': 0}}
    >>> unit_propagation([1, 2, 3, 4], {2: False, 3: False, 4: False})
    {2: False, 3: False, 4: False, 1: True}
    >>> unit_propagation([1, 2, 3, -4], {1: False, 2: False, 3: False})
    {1: False, 2: False, 3: False, 4: False}
    >>> unit_propagation([-1, 2, 3, 4], {2: False, 3: False, 4: False})
    {2: False, 3: False, 4: False, 1: False}
    >>> unit_propagation([1, 2, 3, 4], {2: False, 3: False})
    {2: False, 3: False}
    """
    # TODO: add tests to _init
    pass


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


class SATSolver:
    def __init__(self, formula=None, assignment=None, assignment_by_level=None, max_new_clauses=float('inf'), halving_period=100):
        """
        >>> clause1 = frozenset({1})
        >>> solver = SATSolver(set({clause1}))
        >>> solver._assignment == {1: {'value': True, 'clause': clause1, 'level': 0, 'idx': 0}}
        True
        >>> clause2 = frozenset({1, 2})
        >>> solver = SATSolver(set({clause1, clause2}))
        >>> solver._assignment == {1: {'value': True, 'clause': clause1, 'level': 0, 'idx': 0}}
        True
        """
        if formula is None:
            formula = set()
        if assignment is None:
            assignment = dict()
        if assignment_by_level is None:
            assignment_by_level = []

        self._formula = SATSolver._preprocessing(formula)
        self._new_clauses = deque()
        self._max_new_clauses = max_new_clauses
        self._assignment = assignment
        self._assignment_by_level = assignment_by_level
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

        self._create_new_level()
        for clause in self._formula:
            self._add_literals(clause)
        for clause in self._formula:
            self._add_clause(clause)

    @staticmethod
    def _preprocessing(cnf_formula):
        """
        :param cnf_formula: a formula, in CNF.
        :return: processed formula.
        >>> SATSolver._preprocessing(frozenset({frozenset({})}))
        frozenset()
        >>> SATSolver._preprocessing(frozenset({frozenset({1})}))
        frozenset({frozenset({1})})
        >>> SATSolver._preprocessing(frozenset({frozenset({1}), frozenset({2})}))
        frozenset({frozenset({2}), frozenset({1})})
        >>> SATSolver._preprocessing(frozenset({frozenset({2, 1}), frozenset({3, 4})}))
        frozenset({frozenset({3, 4}), frozenset({1, 2})})
        >>> SATSolver._preprocessing(frozenset({frozenset({1, 2, 1, 1, 2}), frozenset({3, 4})}))
        frozenset({frozenset({3, 4}), frozenset({1, 2})})
        >>> SATSolver._preprocessing(frozenset({frozenset({1, 2, 1, 1, 2, -1}), frozenset({3, 4})}))
        frozenset({frozenset({3, 4})})
        >>> SATSolver._preprocessing(frozenset({frozenset({1, -1}), frozenset({3, -4})}))
        frozenset({frozenset({3, -4})})
        >>> SATSolver._preprocessing(frozenset({frozenset({2, 1, -1}), frozenset({3, -4})}))
        frozenset({frozenset({3, -4})})
        >>> SATSolver._preprocessing(frozenset({frozenset({1, 2, -1}), frozenset({3, -4})}))
        frozenset({frozenset({3, -4})})
        >>> SATSolver._preprocessing(frozenset({frozenset({1, -1, 2}), frozenset({3, -4})}))
        frozenset({frozenset({3, -4})})
        >>> SATSolver._preprocessing(frozenset({frozenset({1, 1, 2, 3, 3, -4}), frozenset({3, -4, 1, 2})}))
        frozenset({frozenset({1, 2, 3, -4})})
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

    def _add_literal(self, clause, literal):
        if literal not in self._literal_to_clause:
            self._literal_to_clause[literal] = set()
            self._literal_to_watched_clause[literal] = set()
            self._unassigned_vsids_count[literal] = 0
        self._literal_to_clause[literal].add(clause)

    def _add_literals(self, clause):
        for literal in clause:
            self._add_literal(clause, literal)

    def _add_clause(self, clause):
        for literal in clause:
            if literal in self._unassigned_vsids_count:
                self._unassigned_vsids_count[literal] += 1
            elif literal in self._assigned_vsids_count:
                self._assigned_vsids_count[literal] += 1
        self._unit_propagation(clause)
        self._create_watch_literals(clause)

    def _create_new_level(self):
        self._assignment_by_level.append(list())
        self._satisfaction_by_level.append(list())

    def _unit_propagation(self, clause):
        if len(clause) == 1:
            for literal in clause:
                if abs(literal) not in self._assignment:
                    self._assign_to_satisfy(clause, literal)

    def _assign_watch_literal(self, clause, literal: int):
        self._literal_to_watched_clause[literal].add(clause)

    def _create_watch_literals(self, clause):
        count = 0
        for literal in clause:
            self._assign_watch_literal(clause, literal)
            count += 1
            if count > 1:
                return

    def _assign(self, variable: int, value: bool, clause) -> bool:
        self._assignment[variable] = {
            "value": value,     # True or False
            "clause": clause,   # The clause which caused the assignment
            "level": len(self._assignment_by_level) - 1,
            "idx": len(self._assignment_by_level[-1])   # Defines an assignment order in the same level
        }

        # Keep data structures related to variable assignment up to date
        self._assignment_by_level[-1].append(variable)
        self._last_assigned_literals.append(variable)
        if -variable in self._literal_to_clause:
            self._last_assigned_literals.append(-variable)

        for literal in [variable, -variable]:
            if literal in self._unassigned_vsids_count:
                self._assigned_vsids_count[literal] = self._unassigned_vsids_count[literal]
                del self._unassigned_vsids_count[literal]

        # Keep data structures related to satisfied clauses up to date
        if (variable > 0) == value:
            literal = variable
        else:
            literal = -variable
        self._satisfaction_by_level[-1].extend(self._literal_to_clause[literal] - self._satisfied_clauses)
        self._satisfied_clauses |= self._literal_to_clause[literal]
        return True

    def _assign_to_satisfy(self, clause, literal: int):
        return self._assign(abs(literal), literal > 0, clause)

    def _unassign(self, variable):
        del self._assignment[variable]

        for literal in [variable, -variable]:
            if literal in self._assigned_vsids_count:
                self._unassigned_vsids_count[literal] = self._assigned_vsids_count[literal]
                del self._assigned_vsids_count[literal]

    def _get_assignment(self, variable: int):
        return self._assignment[variable]["value"]

    def _get_assignment_level(self, variable: int):
        return self._assignment[variable]["level"]

    def _get_assignment_idx(self, variable: int):
        return self._assignment[variable]["idx"]

    def _get_assignment_clause(self, variable: int):
        return self._assignment[variable]["clause"]

    def _conflict_resolution(self, conflict_clause):
        """
        >>> clause1 = frozenset({1})
        >>> clause3 = frozenset({-1, 2})
        >>> clause5 = frozenset({-1, -2})
        >>> solver = SATSolver(set({clause1, clause3, clause5}))
        >>> solver._conflict_resolution(solver._bcp()) == (frozenset({-1}), -1, -1)
        True
        >>> clause1 = frozenset({-1, -4, 5})
        >>> clause2 = frozenset({-4, 6})
        >>> clause3 = frozenset({-5, -6, 7})
        >>> clause4 = frozenset({-7, 8})
        >>> clause5 = frozenset({-2, -7, 9})
        >>> clause6 = frozenset({-8, -9})
        >>> clause7 = frozenset({-8, 9})
        >>> formula = set({clause1, clause2, clause3, clause4, clause5, clause6, clause7})
        >>> assignment = {
        ... 1: {"value": True, "clause": None, "level": 1, "idx": 1},
        ... 2: {"value": True, "clause": None, "level": 2, "idx": 1},
        ... 3: {"value": True, "clause": None, "level": 3, "idx": 1},
        ... 4: {"value": True, "clause": None, "level": 4, "idx": 1},
        ... }
        >>> solver = SATSolver(formula, assignment=assignment)
        >>> solver._assignment_by_level = [[], [1], [2], [3], [4]]
        >>> solver._last_assigned_literals.append(-4)
        >>> solver._literal_to_watched_clause[-4] = set({clause1, clause2})
        >>> solver._literal_to_watched_clause[-5] = set({clause3})
        >>> solver._literal_to_watched_clause[-6] = set({clause3})
        >>> solver._literal_to_watched_clause[-7] = set({clause4, clause5})
        >>> solver._literal_to_watched_clause[-8] = set({clause6})
        >>> solver._literal_to_watched_clause[-9] = set({clause6})
        >>> solver._conflict_resolution(solver._bcp()) == (frozenset({-7, -2}), -7, 2)
        True
        """
        conflict_clause = set(conflict_clause)
        last_decision_literal = self._assignment_by_level[-1][0]
        while True:
            last_literal, last_variable, prev_max_level, max_level, max_idx, max_count = None, None, -1, -1, -1, 0
            for literal in conflict_clause:
                variable = abs(literal)
                level, idx = self._get_assignment_level(variable), self._get_assignment_idx(variable)
                if level > max_level:
                    prev_max_level = max_level
                    max_level, max_idx, max_count = level, -1, 0
                elif level > prev_max_level:
                    prev_max_level = level
                if level == max_level:
                    max_count += 1
                    if idx > max_idx:
                        last_literal, last_variable, max_idx = literal, variable, idx

            if max_count == 1:
                # The last assigned literal is the only one from the last decision level
                # Return the conflict clause, the next literal to assign (which should be the watch literal of the
                # conflict clause), and the decision level to jump to
                return frozenset(conflict_clause), last_literal, prev_max_level

            # Resolve the conflict clause with the clause on the incoming edge
            conflict_clause |= self._get_assignment_clause(last_variable)
            conflict_clause.remove(last_variable)
            conflict_clause.remove(-last_variable)

    def _bcp(self):
        """
        >>> solver = SATSolver()
        >>> solver._bcp() is None
        True
        >>> solver._assignment
        {}
        >>> clause1 = frozenset({1})
        >>> solver = SATSolver(set({clause1}))
        >>> solver._bcp() is None
        True
        >>> clause2 = frozenset({1, 2})
        >>> solver = SATSolver(set({clause1, clause2}))
        >>> solver._bcp() is None
        True
        >>> solver._assignment == {1: {"value": True, "clause": clause1, "level": 0, "idx": 0}}
        True
        >>> clause3 = frozenset({-1, 2})
        >>> solver = SATSolver(set({clause1, clause3}))
        >>> solver._bcp() is None
        True
        >>> solver._assignment == {
        ... 1: {"value": True, "clause": clause1, "level": 0, "idx": 0},
        ... 2: {"value": True, "clause": clause3, "level": 0, "idx": 1}}
        True
        >>> clause4 = frozenset({-2})
        >>> solver = SATSolver(set({clause1, clause3, clause4}))
        >>> solver._bcp() == clause3
        True
        >>> clause5 = frozenset({-1, -2})
        >>> solver = SATSolver(set({clause1, clause3, clause5}))
        >>> solver._bcp() == clause5
        True
        >>> clause1 = frozenset({-1, -4, 5})
        >>> clause2 = frozenset({-4, 6})
        >>> clause3 = frozenset({-5, -6, 7})
        >>> clause4 = frozenset({-7, 8})
        >>> clause5 = frozenset({-2, -7, 9})
        >>> clause6 = frozenset({-8, -9})
        >>> clause7 = frozenset({-8, 9})
        >>> formula = set({clause1, clause2, clause3, clause4, clause5, clause6, clause7})
        >>> assignment = {
        ... 1: {"value": True, "clause": None, "level": 1, "idx": 1},
        ... 2: {"value": True, "clause": None, "level": 2, "idx": 1},
        ... 3: {"value": True, "clause": None, "level": 3, "idx": 1},
        ... 4: {"value": True, "clause": None, "level": 4, "idx": 1},
        ... }
        >>> solver = SATSolver(formula, assignment=assignment)
        >>> solver._assignment_by_level = [[], [1], [2], [3], [4]]
        >>> solver._last_assigned_literals.append(-4)
        >>> solver._literal_to_watched_clause[-4] = set({clause1, clause2})
        >>> solver._literal_to_watched_clause[-5] = set({clause3})
        >>> solver._literal_to_watched_clause[-6] = set({clause3})
        >>> solver._literal_to_watched_clause[-7] = set({clause4, clause5})
        >>> solver._literal_to_watched_clause[-8] = set({clause6})
        >>> solver._literal_to_watched_clause[-9] = set({clause6})
        >>> solver._bcp() == clause6
        True
        """
        seen_literals = set()   # Avoid going over literals more than once
        while self._last_assigned_literals:
            watch_literal = self._last_assigned_literals.popleft()
            if (watch_literal in seen_literals) or (watch_literal not in self._literal_to_watched_clause) or \
                    (self._get_assignment(abs(watch_literal)) == (watch_literal > 0)):
                continue
            seen_literals.add(watch_literal)

            for clause in (self._literal_to_watched_clause[watch_literal] - self._satisfied_clauses).copy():
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
                self._assign_watch_literal(clause, unassigned_literal)

        if len(unassigned_literals) == 0:
            # Clause is UNSAT, return it as the conflict-clause
            return clause
        if len(unassigned_literals) == 1:
            # The clause is still not satisfied, and has only one unassigned literal.
            # Assign the correct value to it. Because it is now watching the clause,
            # and was also added to self._last_assigned_literals, we will later on
            # check if the assignment causes a conflict
            if not self._assign_to_satisfy(clause, unassigned_literals.pop()):
                return clause
        return None

    def _add_conflict_clause(self, conflict_clause, literal_to_assign):
        if self._max_new_clauses <= 0:
            return

        # Remove previous conflict clauses, if there are too many
        if len(self._new_clauses) == self._max_new_clauses:
            clause_to_remove = self._new_clauses.popleft()
            for literal in clause_to_remove:
                if literal in self._literal_to_watched_clause:
                    self._literal_to_watched_clause[literal].discard(clause_to_remove)

        self._new_clauses.append(conflict_clause)
        self._add_literals(conflict_clause)
        self._add_clause(conflict_clause)
        self._assign_to_satisfy(conflict_clause, literal_to_assign)

    def _backtrack(self, level: int):
        self._last_assigned_literals = deque()
        while len(self._assignment_by_level) > level + 1:
            for variable in self._assignment_by_level.pop():
                self._unassign(variable)
            for clause in self._satisfaction_by_level.pop():
                self._satisfied_clauses.remove(clause)

    def _decide(self) -> int:
        """

        """
        # Maintain data structures related to VSIDS
        self._decision_counter += 1
        if self._decision_counter >= self._halving_period:
            for literal in self._unassigned_vsids_count:
                self._unassigned_vsids_count[literal] /= 2
            for literal in self._assigned_vsids_count:
                self._assigned_vsids_count[literal] /= 2

        literal, count = self._unassigned_vsids_count.most_common(1).pop()
        return literal

    def get_assignment(self):
        return {variable: self._get_assignment(variable) for variable in self._assignment}

    def solve(self) -> bool:
        """
        >>> SATSolver().solve()
        True
        >>> clause1 = frozenset({1})
        >>> SATSolver(set({clause1})).solve()
        True
        >>> clause2 = frozenset({-1})
        >>> SATSolver(set({clause1, clause2})).solve()
        False
        >>> clause3 = frozenset({1, 2})
        >>> SATSolver(set({clause1, clause3})).solve()
        True
        >>> clause4 = frozenset({-1, 2})
        >>> SATSolver(set({clause1, clause4})).solve()
        True
        >>> clause5 = frozenset({-1, 2, -2})
        >>> SATSolver(set({clause1, clause5})).solve()
        True
        >>> SATSolver(set({clause1, clause3, clause4, clause5})).solve()
        True
        >>> clause1 = frozenset({-1, -4, 5})
        >>> clause2 = frozenset({-4, 6})
        >>> clause3 = frozenset({-5, -6, 7})
        >>> clause4 = frozenset({-7, 8})
        >>> clause5 = frozenset({-2, -7, 9})
        >>> clause6 = frozenset({-8, -9})
        >>> clause7 = frozenset({-8, 9})
        >>> solver = SATSolver(set({clause1, clause2, clause3, clause4, clause5, clause6, clause7}))
        >>> solver.solve()
        True
        >>> assignment = solver.get_assignment()
        >>> assignment[4]
        False
        >>> assignment[6]
        False
        >>> assignment[7]
        False
        >>> assignment[8]
        False
        >>> assignment[9]
        True
        >>> clause1 = frozenset({5, -1, 3})
        >>> clause2 = frozenset({-1, -5})
        >>> clause3 = frozenset({-3, -4})
        >>> clause4 = frozenset({1, 4})
        >>> clause5 = frozenset({1, -4})
        >>> clause6 = frozenset({-1, 5})
        >>> SATSolver(set({clause1, clause2, clause3, clause4, clause5, clause6})).solve()
        False

        :return: True if SAT, False otherwise.
        """
        while True:
            # Iterative BCP
            conflict_clause = self._bcp()
            while conflict_clause is not None:
                conflict_clause, watch_literal, level_to_jump_to = self._conflict_resolution(conflict_clause)
                if level_to_jump_to == -1:
                    # One of the assignments that satisfy the formula's unit clauses causes a conflict, the formula is UNSAT
                    return False
                self._backtrack(level_to_jump_to)
                self._add_conflict_clause(conflict_clause, watch_literal)
                conflict_clause = self._bcp()

            if self._formula.issubset(self._satisfied_clauses):
                # If all clauses are satisfied, we are done
                return True

            self._create_new_level()
            literal_to_assign = self._decide()
            self._assign_to_satisfy(None, literal_to_assign)
