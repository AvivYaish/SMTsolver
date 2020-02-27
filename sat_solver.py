

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
    ({'not (=> (not (and p q)) (not r))': 1, '=> (not (and p q)) (not r)': 2, 'not (and p q)': 3, 'not r': 4, 'r': 5, 'and p q': 6, 'p': 7, 'q': 8}, {1: {frozenset({-1, -2}), frozenset({1, 2})}, 2: {frozenset({2, -4}), frozenset({2, 3}), frozenset({4, -3, -2})}, 4: {frozenset({-5, -4}), frozenset({4, 5})}, 3: {frozenset({-6, -3}), frozenset({3, 6})}, 6: {frozenset({8, -6}), frozenset({-8, -7, 6}), frozenset({-6, 7})}}, {frozenset({2, 3}), frozenset({1, 2}), frozenset({-8, -7, 6}), frozenset({4, 5}), frozenset({-6, -3}), frozenset({3, 6}), frozenset({4, -3, -2}), frozenset({-1, -2}), frozenset({8, -6}), frozenset({-5, -4}), frozenset({-6, 7}), frozenset({2, -4})})
    >>> tseitin_tranform("not (=> (not (and pq78 q)) (not r))")
    ({'not (=> (not (and pq78 q)) (not r))': 1, '=> (not (and pq78 q)) (not r)': 2, 'not (and pq78 q)': 3, 'not r': 4, 'r': 5, 'and pq78 q': 6, 'pq78': 7, 'q': 8}, {1: {frozenset({-1, -2}), frozenset({1, 2})}, 2: {frozenset({2, -4}), frozenset({2, 3}), frozenset({4, -3, -2})}, 4: {frozenset({-5, -4}), frozenset({4, 5})}, 3: {frozenset({-6, -3}), frozenset({3, 6})}, 6: {frozenset({8, -6}), frozenset({-8, -7, 6}), frozenset({-6, 7})}}, {frozenset({2, 3}), frozenset({1, 2}), frozenset({-8, -7, 6}), frozenset({4, 5}), frozenset({-6, -3}), frozenset({3, 6}), frozenset({4, -3, -2}), frozenset({-1, -2}), frozenset({8, -6}), frozenset({-5, -4}), frozenset({-6, 7}), frozenset({2, -4})})
    """
    # TODO: this both parses and does the transform, should split to 2 functions
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
            # transformed_subformulas[subformulas[cur_formula]] = [[subformulas[left_side]], [subformulas[right_side]]]
            transformed_subformulas[subformulas[cur_formula]] = {
                frozenset({-subformulas[cur_formula], subformulas[left_side]}),
                frozenset({-subformulas[cur_formula], subformulas[right_side]}),
                frozenset({-subformulas[left_side], -subformulas[right_side], subformulas[cur_formula]}),
            }
        elif operator == "or":
            # transformed_subformulas[subformulas[cur_formula]] = [subformulas[left_side], subformulas[right_side]]
            transformed_subformulas[subformulas[cur_formula]] = {
                frozenset({-subformulas[cur_formula], subformulas[left_side], subformulas[right_side]}),
                frozenset({-subformulas[left_side], subformulas[cur_formula]}),
                frozenset({-subformulas[right_side], subformulas[cur_formula]})
            }
        elif operator == "=>":
            # transformed_subformulas[subformulas[cur_formula]] = [-subformulas[left_side], subformulas[right_side]]
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
    preprocessed_formula = set()
    for clause in cnf_formula:
        trivial_clause = False
        for literal in clause:
            if -literal in clause:
                # Remove trivial clauses
                # If the same variable appears twice with
                # different sign in the same clause
                trivial_clause = True
                break

        if trivial_clause or (len(clause) == 0):
            # Remove empty clauses
            continue

        preprocessed_formula.add(clause)

    return frozenset(preprocessed_formula)


def unit_propagation(clause, assignment, level):
    """
    >>> unit_propagation([], {})
    {}
    >>> unit_propagation([1], {})
    {1: True}
    >>> unit_propagation([-1], {})
    {1: False}
    >>> unit_propagation([-1], {1: True})
    {1: True}
    >>> unit_propagation([-1], {1: False})
    {1: False}
    >>> unit_propagation([1, 2, 3, 4], {1: False, 2: False, 3: False})
    {1: False, 2: False, 3: False, 4: True}
    >>> unit_propagation([1, 2, 3, 4], {2: False, 3: False, 4: False})
    {2: False, 3: False, 4: False, 1: True}
    >>> unit_propagation([1, 2, 3, -4], {1: False, 2: False, 3: False})
    {1: False, 2: False, 3: False, 4: False}
    >>> unit_propagation([-1, 2, 3, 4], {2: False, 3: False, 4: False})
    {2: False, 3: False, 4: False, 1: False}
    >>> unit_propagation([1, 2, 3, 4], {2: False, 3: False})
    {2: False, 3: False}
    """
    unassigned = []
    # TODO: maybe better to do this in numpy?
    #
    for literal in clause:
        if abs(literal) not in assignment:
            if len(unassigned) == 1:
                return assignment
            unassigned.append(literal)

    literal = unassigned.pop()
    assignment[abs(literal)] = {
        "value": (literal > 0),
        "clause": clause,
        "level": level
    }
    return assignment


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
    def __init__(self, formula):
        self._formula = formula

    def solve(self, assignment) -> bool:
        """
        :return: True if SAT, False otherwise.
        """
        # BCP
        for clause in self._formula:
            # assignment is changed in place
            # this is OK because we copy it before the recursive call
            unit_propagation(clause, assignment)


        return False
