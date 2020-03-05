from collections import deque
from itertools import chain


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


def preprocessing(cnf_formula):
    """
    :param cnf_formula: a formula, in CNF.
    :return: processed formula.
    >>> preprocessing(frozenset({frozenset({})}))
    frozenset()
    >>> preprocessing(frozenset({frozenset({1})}))
    frozenset({frozenset({1})})
    >>> preprocessing(frozenset({frozenset({1}), frozenset({2})}))
    frozenset({frozenset({2}), frozenset({1})})
    >>> preprocessing(frozenset({frozenset({2, 1}), frozenset({3, 4})}))
    frozenset({frozenset({3, 4}), frozenset({1, 2})})
    >>> preprocessing(frozenset({frozenset({1, 2, 1, 1, 2}), frozenset({3, 4})}))
    frozenset({frozenset({3, 4}), frozenset({1, 2})})
    >>> preprocessing(frozenset({frozenset({1, 2, 1, 1, 2, -1}), frozenset({3, 4})}))
    frozenset({frozenset({3, 4})})
    >>> preprocessing(frozenset({frozenset({1, -1}), frozenset({3, -4})}))
    frozenset({frozenset({3, -4})})
    >>> preprocessing(frozenset({frozenset({2, 1, -1}), frozenset({3, -4})}))
    frozenset({frozenset({3, -4})})
    >>> preprocessing(frozenset({frozenset({1, 2, -1}), frozenset({3, -4})}))
    frozenset({frozenset({3, -4})})
    >>> preprocessing(frozenset({frozenset({1, -1, 2}), frozenset({3, -4})}))
    frozenset({frozenset({3, -4})})
    >>> preprocessing(frozenset({frozenset({1, 1, 2, 3, 3, -4}), frozenset({3, -4, 1, 2})}))
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
    # TODO: maybe better to do this in numpy?
    # TODO: 1. change tests to receive frozensets
    #  2. assignment should receive dictionary that includes clauses and levels
    #  3. should add a "parent" pointer for each assigned variable
    unassigned = []
    for literal in clause:
        if abs(literal) not in assignment:
            if len(unassigned) == 1:
                return assignment
            unassigned.append(literal)

    if unassigned:
        literal = unassigned.pop()
        assignment[abs(literal)] = {
            "value": (literal > 0),
            "clause": clause,
            "level": level
        }

    # TODO: return if there is a conflict?
    return None


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
    def __init__(self, formula=None, assignment=None, assignment_by_level=None, max_new_clauses=100):
        """
        >>> clause1 = frozenset({1})
        >>> solver = SATSolver(set({clause1}))
        >>> solver._assignment == {1: {'value': True, 'clause': clause1, 'level': 0}}
        True
        >>> clause2 = frozenset({1, 2})
        >>> solver = SATSolver(set({clause1, clause2}))
        >>> solver._assignment == {1: {'value': True, 'clause': clause1, 'level': 0}}
        True
        """
        if formula is None:
            formula = set()
        if assignment is None:
            assignment = dict()
        if assignment_by_level is None:
            assignment_by_level = []

        self._formula = formula
        self._new_clauses = deque()
        self._max_new_clauses = max_new_clauses
        self._assignment = assignment
        self._assignment_by_level = assignment_by_level
        self._satisfaction_by_level = []
        self._satisfied_clauses = set()
        self._level = len(self._assignment_by_level)
        self._last_assigned_literals = deque()               # a queue of the literals assigned in the last level
        self._watch_literal_to_clause = {}                   # A literal -> set(clause) dictionary.
        self._unit_clauses = set()
        self._add_watch_literals()

    def _add_watch_literals(self):
        for clause in self._formula:
            for idx, literal in enumerate(clause):
                if literal not in self._watch_literal_to_clause:
                    self._watch_literal_to_clause[literal] = set()
                if -literal not in self._watch_literal_to_clause:
                    self._watch_literal_to_clause[-literal] = set()

                if idx == (len(clause) - 1):
                    self._watch_literal_to_clause[literal].add(clause)
                    if idx == 0:    # unit clause
                        self._assign(abs(literal), literal > 0, clause)
                elif idx == (len(clause) - 2):
                    self._watch_literal_to_clause[literal].add(clause)

        # Whenever there is a backjump to level k:
        # - For every index after k-1:
        #   - For every variable that was assigned on this level:
        #       - For every clause in self._historical_last_watch_literal[variable]:
        #           - Add clause to self._last_watch_literal[variable]
        #           - Remove clause from self._historical_last_watch_literal[variable]
        #       - For every clause in self._historical_second_last_watch_literal[variable]:
        #           - Add clause to self._second_last_watch_literal[variable]
        #           - Remove clause from self._historical_second_last_watch_literal[variable]
        #       - Remove the variable from self._assignment
        #   - For every clause that was satisfied on this level:
        #       - Remove it from self._satisfied_clauses
        #   - Delete the index from self._assignment_by_level
        #   - Delete the index from self._satisfaction_by_level

    def _assign(self, variable, value, clause):
        self._assignment[variable] = {
            "value": value,     # True or False
            "clause": clause,   # The clause which caused the assignment
            "level": self._level
        }
        self._assignment_by_level[-1].append(variable)
        self._last_assigned_literals.append(variable)
        self._last_assigned_literals.append(-variable)

    def _get_assignment(self, variable):
        return self._assignment[variable]["value"]

    def _get_assignment_level(self, variable):
        return self._assignment[variable]["level"]

    def _get_assignment_clause(self, variable):
        return self._assignment[variable]["clause"]

    def _conflict_resolution(self, clause):
        while True:
            last_assigned_literal = None
            previous_max_assignment_level = -1
            max_assignment_level = -1
            number_of_max_literals = 0
            for literal in clause:
                variable = abs(literal)
                level = self._get_assignment_level(variable)
                if level > max_assignment_level:
                    previous_max_assignment_level = max_assignment_level
                    max_assignment_level = level
                    last_assigned_literal = variable
                    number_of_max_literals = 1
                elif level == max_assignment_level:
                    number_of_max_literals += 1

            if number_of_max_literals == 1:
                return {
                    "conflict_clause": clause,
                    "variable": last_assigned_literal,
                    "value": -self._get_assignment(last_assigned_literal),
                    "level": previous_max_assignment_level  # The lowest level possible
                }

            # Resolving the two clauses
            clause_on_incoming_edge = self._get_assignment_clause(last_assigned_literal)
            new_clause = set()
            for literal in chain(clause, clause_on_incoming_edge):
                if -literal in new_clause:
                    new_clause.remove(-literal)
                    continue
                new_clause.add(literal)
            clause = new_clause

    def _bcp(self):
        """
        # >>> solver = SATSolver()
        # >>> solver._bcp() is None
        # True
        # >>> solver._assignment
        # {}
        >>> clause1 = frozenset({1})
        >>> solver = SATSolver(set({clause1}))
        >>> solver._bcp() is None
        True
        >>> solver = SATSolver(set({frozenset({1}), frozenset({1, 2})}))
        >>> solver._bcp() is None
        True
        >>> solver._assignment
        {1: {"value": True, "clause": clause1, "level": 0}}
        """
        # Avoid going over literals more than once
        seen_literals = set()

        while self._last_assigned_literals:
            cur_literal = self._last_assigned_literals.popleft()
            if cur_literal in seen_literals:
                continue
            seen_literals.add(cur_literal)

            #
            for clause in self._watch_literal_to_clause[cur_literal]:
                if self._get_assignment(abs(cur_literal)) == (cur_literal > 0):
                    self._satisfied_clauses.add(clause)
                    self._satisfaction_by_level[-1].add(clause)
                if clause not in self._satisfied_clauses:
                    unassigned_literals = []
                    for literal in clause:
                        if abs(literal) in self._assignment:
                            continue
                        unassigned_literals.append(literal)
                        if clause in self._watch_literal_to_clause[literal]:
                            continue
                        self._watch_literal_to_clause[-cur_literal].remove(clause)
                        self._watch_literal_to_clause[literal].add(clause)
                    if len(unassigned_literals) == 0:
                        # Clause is UNSAT, return it as the conflict-clause
                        return clause
                    if len(unassigned_literals) == 1:
                        unassigned_literal = unassigned_literals.pop()
                        self._assign(abs(unassigned_literal), unassigned_literal > 0, clause)
        return None # No conflict-clause

    def solve(self, assignment) -> bool:
        """
        :return: True if SAT, False otherwise.
        """
        self._bcp()
        # SHOULD IMPELEMENT VSIDS, ITS EASIER
        return False
