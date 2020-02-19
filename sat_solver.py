

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
    ({'not (=> (not (and p q)) (not r))': 1, '=> (not (and p q)) (not r)': 2, 'not (and p q)': 3, 'not r': 4, 'r': 5, 'and p q': 6, 'p': 7, 'q': 8}, {1: [[-1, -2], [1, 2]], 2: [[-2, -3, 4], [3, 2], [-4, 2]], 4: [[-4, -5], [4, 5]], 3: [[-3, -6], [3, 6]], 6: [[-6, 7], [-6, 8], [-7, -8, 6]]})
    >>> tseitin_tranform("not (=> (not (and pq78 q)) (not r))")
    ({'not (=> (not (and pq78 q)) (not r))': 1, '=> (not (and pq78 q)) (not r)': 2, 'not (and pq78 q)': 3, 'not r': 4, 'r': 5, 'and pq78 q': 6, 'pq78': 7, 'q': 8}, {1: [[-1, -2], [1, 2]], 2: [[-2, -3, 4], [3, 2], [-4, 2]], 4: [[-4, -5], [4, 5]], 3: [[-3, -6], [3, 6]], 6: [[-6, 7], [-6, 8], [-7, -8, 6]]})
    """
    # TODO: this both parses and does the transform, should split to 2 functions
    formula_list = [formula]
    subformulas = {}
    transformed_subformulas = {}
    transformed_formula = []
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

            transformed_subformulas[subformulas[cur_formula]] = [
                [-subformulas[cur_formula], -subformulas[right_side]],
                [subformulas[cur_formula], subformulas[right_side]]
            ]
            transformed_formula += transformed_subformulas[subformulas[cur_formula]]
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
            transformed_subformulas[subformulas[cur_formula]] = [
                [-subformulas[cur_formula], subformulas[left_side]],
                [-subformulas[cur_formula], subformulas[right_side]],
                [-subformulas[left_side], -subformulas[right_side], subformulas[cur_formula]],
            ]
        elif operator == "or":
            # transformed_subformulas[subformulas[cur_formula]] = [subformulas[left_side], subformulas[right_side]]
            transformed_subformulas[subformulas[cur_formula]] = [
                [-subformulas[cur_formula], subformulas[left_side], subformulas[right_side]],
                [-subformulas[left_side], subformulas[cur_formula]],
                [-subformulas[right_side], subformulas[cur_formula]]
            ]
        elif operator == "=>":
            # transformed_subformulas[subformulas[cur_formula]] = [-subformulas[left_side], subformulas[right_side]]
            transformed_subformulas[subformulas[cur_formula]] = [
                [-subformulas[cur_formula], -subformulas[left_side], subformulas[right_side]],
                [subformulas[left_side], subformulas[cur_formula]],
                [-subformulas[right_side], subformulas[cur_formula]]
            ]
        elif operator == "<=>":
            # TODO: add tests for this
            transformed_subformulas[subformulas[cur_formula]] = [
                # =>
                [-subformulas[cur_formula], -subformulas[left_side], subformulas[right_side]],
                [subformulas[left_side], subformulas[cur_formula]],
                [-subformulas[right_side], subformulas[cur_formula]],
                # <=
                [subformulas[cur_formula], subformulas[left_side], subformulas[right_side]],
                [subformulas[cur_formula], -subformulas[left_side], -subformulas[right_side]]
            ]
        transformed_formula += transformed_subformulas[subformulas[cur_formula]]
    return subformulas, transformed_subformulas, transformed_formula


def preprocessing(cnf_formula):
    """
    :param cnf_formula: a formula, in CNF.
    :return: processed formula.
    >>> preprocessing([[]])
    []
    >>> preprocessing([[1]])
    [[1]]
    >>> preprocessing([[1], [2]])
    [[1], [2]]
    >>> preprocessing([[1, 2], [3, 4]])
    [[1, 2], [3, 4]]
    >>> preprocessing([[1, 2, 1, 1, 2], [3, 4]])
    [[1, 2], [3, 4]]
    >>> preprocessing([[1, 2, 1, 1, 2, -1], [3, 4]])
    [[3, 4]]
    >>> preprocessing([[1, -1], [3, -4]])
    [[3, -4]]
    >>> preprocessing([[2, 1, -1], [3, -4]])
    [[3, -4]]
    >>> preprocessing([[1, 2, -1], [3, -4]])
    [[3, -4]]
    >>> preprocessing([[1, -1, 2], [3, -4]])
    [[3, -4]]
    """
    clause_idx = 0
    while clause_idx < len(cnf_formula):
        clause = cnf_formula[clause_idx]

        if len(clause) == 0:
            # Remove empty clauses
            last_clause = cnf_formula.pop()
            if clause_idx < len(cnf_formula):
                cnf_formula[clause_idx] = last_clause
            continue

        seen_literals = set()
        literal_idx = 0
        while literal_idx < len(clause):
            literal = clause[literal_idx]
            if -literal in seen_literals:
                # Remove trivial clauses
                # If the same variable appears twice with
                # different sign in the same clause
                last_clause = cnf_formula.pop()
                if clause_idx < len(cnf_formula):
                    cnf_formula[clause_idx] = last_clause
                clause_idx -= 1
                break
            elif literal not in seen_literals:
                seen_literals.add(literal)
                literal_idx += 1
            else:
                # Remove redundant literals
                # If the same variable appears twice with
                # the same sign in the same clause
                last_literal = clause.pop()
                if literal_idx < len(clause):
                    clause[literal_idx] = last_literal
        clause_idx += 1

    return cnf_formula


def unit_propagation(clause, assignment):
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
    for literal in clause:
        if abs(literal) not in assignment:
            if len(unassigned) == 1:
                return assignment
            unassigned.append(literal)

    literal = unassigned.pop()
    assignment[abs(literal)] = (literal > 0)
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

        return False
