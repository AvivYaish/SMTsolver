from smt_solver.congruence_graph import CongruenceGraph
import re


class FormulaParser:
    # Assumes variables do not start with a character that is also an operator
    # It would definitely be better to use a Lexer here, but we assumed that parsing was also a part of the project.

    TRUE = 'true'
    FALSE = 'false'

    NOT = 'not'
    AND = 'and'
    OR = 'or'
    IMPLICATION = '=>'
    BICONDITIONAL = '<=>'

    BOOLEAN_CONSTANTS = frozenset({TRUE, FALSE})
    BOOLEAN_UNARY_OPS = frozenset({NOT})
    BOOLEAN_BINARY_OPS = frozenset({AND, OR, IMPLICATION, BICONDITIONAL})
    BOOLEAN_OPS = BOOLEAN_UNARY_OPS | BOOLEAN_BINARY_OPS

    EQUALITY = "="
    UF_OPS = frozenset({EQUALITY})

    ALL_SYMMETRIC_OPS = UF_OPS | {AND, OR, BICONDITIONAL}
    ALL_BINARY_OPS = UF_OPS | BOOLEAN_BINARY_OPS
    ALL_OPS = UF_OPS | BOOLEAN_OPS

    _OPENING_BRACKET = '('
    _CLOSING_BRACKET = ')'
    _PARAMETER_SEPARATOR = ','

    _DECLARATION = re.compile(r'\(\s*declare-fun\s+(\w+)\s+\(([^\)]*)\)\s+(\w+)\s*\)')
    _ASSERTION = re.compile(r'\(\s*assert\s*')
    _FUNCTION_COMMA = re.compile(r'\(.*?\)|(,)')

    @staticmethod
    def symmetric_formula(parsed_formula):
        if ((not parsed_formula) or (len(parsed_formula) < 3) or
                (parsed_formula[0] not in FormulaParser.ALL_SYMMETRIC_OPS)):
            return parsed_formula
        return parsed_formula[0], parsed_formula[2], parsed_formula[1]

    @staticmethod
    def _find_closing_bracket(text: str) -> int:
        """
        :return: the index of the ')' bracket that closes the very first (left-most) '(' bracket.
        """
        flag = False
        counter = 0
        for idx, char in enumerate(text):
            if char == FormulaParser._OPENING_BRACKET:
                flag = True
                counter += 1
            elif char == FormulaParser._CLOSING_BRACKET:
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
        while (formula and (formula[0] == FormulaParser._OPENING_BRACKET) and
               (FormulaParser._find_closing_bracket(formula) == len(formula))):
            formula = formula[1:-1].strip()
        return formula

    @staticmethod
    def _separate_parameters(unparsed_parameters: str):
        parameters = []
        if unparsed_parameters:
            start_idx = 0
            for match in re.finditer(FormulaParser._FUNCTION_COMMA, unparsed_parameters):
                if match.group(0) != FormulaParser._PARAMETER_SEPARATOR:
                    continue
                cur_parameter = unparsed_parameters[start_idx:match.start()]
                parameters.append(cur_parameter)
                start_idx = match.end()
            parameters.append(unparsed_parameters[start_idx:])
        return parameters

    @staticmethod
    def _parse_function_call(unparsed_call: str, unary_operators, signature):
        for function_name in signature:
            if unparsed_call.startswith(function_name):
                parameter_string = FormulaParser._prepare_formula(unparsed_call.split(function_name, 1).pop())
                separated_parameters = FormulaParser._separate_parameters(parameter_string)
                parsed_parameters = [FormulaParser._parse_formula(unparsed_parameter, unary_operators, signature) for
                                     unparsed_parameter in separated_parameters]
                return (function_name, *parsed_parameters)
        return None

    @staticmethod
    def _parse_uf(formula: str, unary_operators=BOOLEAN_UNARY_OPS):
        """
        Assumes asserts and declarations are enclosed by a single ( and ).
        """
        signature = {}
        parsed_formulas = []

        # Parsing function declarations
        for match in re.finditer(FormulaParser._DECLARATION, formula):
            name = match.group(1)
            parameters = match.group(2)
            output = match.group(3)
            signature[name] = {
                "parameter_types": parameters.split(),
                "output_type": output
            }

        # Parsing assertions
        for match in re.finditer(FormulaParser._ASSERTION, formula):
            unparsed_formula = formula[match.end():]
            unparsed_formula = unparsed_formula[:FormulaParser._find_closing_bracket(unparsed_formula)]
            parsed_formulas.append(FormulaParser._parse_formula(unparsed_formula, unary_operators, signature))

        return signature, parsed_formulas

    @staticmethod
    def _parse_formula(formula: str, unary_operators=BOOLEAN_UNARY_OPS, signature=None):
        """
        :return: given a textual representation of an SMT-LIBv2 formula, returns a tuple representation of it:
        (operator, left side, right side (if exists))
        And for functions: (function_name, param1, param2, ...)
        """
        if signature is None:
            signature = {}

        formula = FormulaParser._prepare_formula(formula)
        if not formula:
            return None

        parsed_function_call = FormulaParser._parse_function_call(formula, unary_operators, signature)
        if parsed_function_call is not None:
            return parsed_function_call

        split_cur_formula = formula.split(None, 1)  # Assumes operators are always a single character
        right_side = split_cur_formula.pop()
        if len(split_cur_formula) == 0:
            # Base case, only one variable/boolean value
            return right_side

        operator = split_cur_formula.pop().lower()
        if operator in unary_operators:
            return operator, FormulaParser._parse_formula(right_side, unary_operators, signature)

        # Binary operator
        closing_idx = FormulaParser._find_closing_bracket(right_side)
        if (closing_idx != -1) and (closing_idx != len(right_side)):
            # If the first parameter of the operator is enclosed in brackets, split the first and second parameters
            # according to the location of the closing bracket.
            left_side = FormulaParser._prepare_formula(right_side[:closing_idx])
            right_side = FormulaParser._prepare_formula(right_side[closing_idx:])
        else:
            # The first parameter is not enclosed in brackets and is not a function, can split according to the
            # first whitespace
            left_side, right_side = right_side.split(None, 1)
        return (operator,
                FormulaParser._parse_formula(left_side, unary_operators, signature),
                FormulaParser._parse_formula(right_side, unary_operators, signature))

    @staticmethod
    def _is_parameter_not(parameter):
        return (len(parameter) > 1) and (parameter[0] == FormulaParser.NOT)

    @staticmethod
    def _is_left_not_right(left_parameter, right_parameter):
        return (  # This case is: op (not x) (x)
                (FormulaParser._is_parameter_not(right_parameter) and (right_parameter[1] == left_parameter))
                or
                # This case is: op (not x) (x)
                (FormulaParser._is_parameter_not(left_parameter) and (left_parameter[1] == right_parameter))
        )

    @staticmethod
    def _simplify_formula(parsed_formula):
        # Base case, empty formula
        if not parsed_formula:
            return FormulaParser.TRUE

        operator = parsed_formula[0]
        if operator not in FormulaParser.BOOLEAN_OPS:
            # Base case, only one variable/boolean value
            return parsed_formula

        left_parameter = FormulaParser._simplify_formula(parsed_formula[1])
        if operator == FormulaParser.NOT:
            if FormulaParser._is_parameter_not(left_parameter):
                # not (not x)
                return left_parameter[1]
            if left_parameter == FormulaParser.FALSE:
                return FormulaParser.TRUE
            elif left_parameter == FormulaParser.TRUE:
                return FormulaParser.FALSE
            return operator, left_parameter

        # Binary operator
        right_parameter = FormulaParser._simplify_formula(parsed_formula[2])
        if left_parameter == right_parameter:
            if (operator == FormulaParser.IMPLICATION) or (operator == FormulaParser.BICONDITIONAL):
                return FormulaParser.TRUE
            return left_parameter
        elif (operator == FormulaParser.OR) or (operator == FormulaParser.AND):
            if operator == FormulaParser.OR:
                first_bool, second_bool = FormulaParser.TRUE, FormulaParser.FALSE
            else:
                first_bool, second_bool = FormulaParser.FALSE, FormulaParser.TRUE
            if (
                    # Either: op (x) (first_bool), or: op (first_bool) (x)
                    (left_parameter == first_bool) or (right_parameter == first_bool)
                    or
                    # Either: op (x) (not x), or: op (not x) (x)
                    FormulaParser._is_left_not_right(left_parameter, right_parameter)
            ):
                return first_bool
            if left_parameter == second_bool:
                return right_parameter
            if right_parameter == second_bool:
                return left_parameter
        elif operator == FormulaParser.IMPLICATION:
            if (right_parameter == FormulaParser.TRUE) or (left_parameter == FormulaParser.FALSE):
                return FormulaParser.TRUE
            if right_parameter == FormulaParser.FALSE:
                if left_parameter == FormulaParser.TRUE:
                    return FormulaParser.FALSE
                if left_parameter == FormulaParser.FALSE:
                    return FormulaParser.TRUE
                return FormulaParser.NOT, left_parameter
            if (left_parameter == FormulaParser.TRUE) or \
                    FormulaParser._is_left_not_right(left_parameter, right_parameter):
                return right_parameter
        elif operator == FormulaParser.BICONDITIONAL:
            if left_parameter == FormulaParser.TRUE:
                return right_parameter
            if right_parameter == FormulaParser.TRUE:
                return left_parameter
            if left_parameter == FormulaParser.FALSE:
                if right_parameter == FormulaParser.TRUE:
                    return FormulaParser.FALSE
                if right_parameter == FormulaParser.FALSE:
                    return FormulaParser.TRUE
                return FormulaParser.NOT, right_parameter
            if right_parameter == FormulaParser.FALSE:
                if left_parameter == FormulaParser.TRUE:
                    return FormulaParser.FALSE
                if left_parameter == FormulaParser.FALSE:
                    return FormulaParser.TRUE
                return FormulaParser.NOT, left_parameter
            if FormulaParser._is_left_not_right(left_parameter, right_parameter):
                return FormulaParser.FALSE
        return operator, left_parameter, right_parameter

    @staticmethod
    def _tseitin_transform(parsed_formula,
                           output_all=False,
                           subformulas=None,
                           transformed_subformulas=None,
                           transformed_formula=None):
        """
        Changes all parameters in-place.
        """
        if subformulas is None:
            subformulas = {}
        if transformed_subformulas is None:
            transformed_subformulas = {}
        if transformed_formula is None:
            transformed_formula = set()

        formula_list = [parsed_formula]
        while formula_list:
            cur_formula = formula_list.pop()
            if not cur_formula:
                continue
            operator = cur_formula[0]
            if cur_formula not in subformulas:
                if ((operator in FormulaParser.ALL_SYMMETRIC_OPS) and
                        ((operator, cur_formula[2], cur_formula[1]) in subformulas)):
                    # If a symmetric clause exists, can reuse it
                    cur_formula = (operator, cur_formula[2], cur_formula[1])
                else:
                    subformulas[cur_formula] = len(subformulas) + 1  # + 1 to avoid getting zeros (-0=0)
            if operator not in FormulaParser.BOOLEAN_OPS:
                continue

            left_parameter = cur_formula[1]
            if left_parameter not in subformulas:
                symmetric_left_parameter = FormulaParser.symmetric_formula(left_parameter)
                if symmetric_left_parameter in subformulas:
                    left_parameter = symmetric_left_parameter
                else:
                    subformulas[left_parameter] = len(subformulas) + 1
                    formula_list.append(left_parameter)
            if operator == FormulaParser.NOT:
                transformed_subformulas[subformulas[cur_formula]] = {
                    frozenset({-subformulas[cur_formula], -subformulas[left_parameter]}),
                    frozenset({subformulas[cur_formula], subformulas[left_parameter]})
                }
                transformed_formula |= transformed_subformulas[subformulas[cur_formula]]
                continue

            # Binary operator
            right_parameter = cur_formula[2]
            if right_parameter not in subformulas:
                symmetric_right_parameter = FormulaParser.symmetric_formula(right_parameter)
                if symmetric_right_parameter in subformulas:
                    right_parameter = symmetric_right_parameter
                else:
                    subformulas[right_parameter] = len(subformulas) + 1
                    formula_list.append(right_parameter)
            if operator == FormulaParser.AND:
                transformed_subformulas[subformulas[cur_formula]] = {
                    frozenset({-subformulas[cur_formula], subformulas[left_parameter]}),
                    frozenset({-subformulas[cur_formula], subformulas[right_parameter]}),
                    frozenset({-subformulas[left_parameter], -subformulas[right_parameter], subformulas[cur_formula]}),
                }
            elif operator == FormulaParser.OR:
                transformed_subformulas[subformulas[cur_formula]] = {
                    frozenset({-subformulas[cur_formula], subformulas[left_parameter], subformulas[right_parameter]}),
                    frozenset({-subformulas[left_parameter], subformulas[cur_formula]}),
                    frozenset({-subformulas[right_parameter], subformulas[cur_formula]})
                }
            elif operator == FormulaParser.IMPLICATION:
                transformed_subformulas[subformulas[cur_formula]] = {
                    frozenset({-subformulas[cur_formula], -subformulas[left_parameter], subformulas[right_parameter]}),
                    frozenset({subformulas[left_parameter], subformulas[cur_formula]}),
                    frozenset({-subformulas[right_parameter], subformulas[cur_formula]})
                }
            elif operator == FormulaParser.BICONDITIONAL:
                transformed_subformulas[subformulas[cur_formula]] = {
                    frozenset({-subformulas[cur_formula], -subformulas[left_parameter], subformulas[right_parameter]}),
                    frozenset({-subformulas[cur_formula], subformulas[left_parameter], -subformulas[right_parameter]}),
                    frozenset({subformulas[cur_formula], subformulas[left_parameter], subformulas[right_parameter]}),
                    frozenset({subformulas[cur_formula], -subformulas[left_parameter], -subformulas[right_parameter]}),
                }
            transformed_formula |= transformed_subformulas[subformulas[cur_formula]]

        transformed_formula.add(frozenset({subformulas[parsed_formula]}))  # Always need to satisfy the entire formula
        if output_all:
            return subformulas, transformed_subformulas, transformed_formula
        return transformed_formula

    @staticmethod
    def _preprocess(cnf_formula):
        """
        :param cnf_formula: a formula, in CNF.
        :return: processed formula, with no trivial or empty clauses.
        """
        preprocessed_formula = []
        for clause in cnf_formula:
            trivial_clause = False
            for literal in clause:
                if -literal in clause:
                    # Remove trivial clauses, if the same variable appears twice with different signs in the same clause
                    trivial_clause = True
                    break

            if trivial_clause or (len(clause) == 0):
                # Remove empty clauses
                continue

            preprocessed_formula.append(clause)
        return frozenset(preprocessed_formula)

    @staticmethod
    def _convert_to_cnf(parsed_formula,
                        output_all=False,
                        subformulas=None,
                        transformed_subformulas=None,
                        cnf_formula=None):
        """
        :param cnf_formula: a pre-existing CNF formula, that has an "and" operation between it and parsed_formula.
        :return: a CNF representation of parsed_formula, after simplification, Tseitin, and preprocessing.
        """
        if subformulas is None:
            subformulas = {}
        if transformed_subformulas is None:
            transformed_subformulas = {}
        if cnf_formula is None:
            cnf_formula = set()
        simplified_formula = FormulaParser._simplify_formula(parsed_formula)
        if simplified_formula == FormulaParser.FALSE:
            cnf_formula = frozenset({frozenset({1}), frozenset({-1})})
        else:
            FormulaParser._tseitin_transform(simplified_formula,
                                             subformulas=subformulas,
                                             transformed_subformulas=transformed_subformulas,
                                             transformed_formula=cnf_formula)
        cnf_formula = FormulaParser._preprocess(cnf_formula)
        if output_all:
            return subformulas, transformed_subformulas, cnf_formula
        return cnf_formula

    @staticmethod
    def import_formula(formula: str, output_all=False):
        return FormulaParser._convert_to_cnf(FormulaParser._parse_formula(formula), output_all)

    @staticmethod
    def convert_tseitin_assignment_to_regular(subformulas, assignment):
        variable_to_subformula = {v: k for k, v in subformulas.items()}
        regular_assignment = {}
        for tseitin_variable in assignment:
            if variable_to_subformula[tseitin_variable][0] not in FormulaParser.ALL_OPS:
                regular_assignment[variable_to_subformula[tseitin_variable]] = assignment[tseitin_variable]
        return regular_assignment

    @staticmethod
    def _create_boolean_abstraction(parsed_formula, signature, abstraction=None, non_boolean_clauses=None):
        """
        :param abstraction: a dictionary that will hold the abstraction. It is update in-place, so an empty
        dictionary must be passed as an argument!
        :return: the abstracted formula.
        """
        if abstraction is None:
            abstraction = {}
        if non_boolean_clauses is None:
            non_boolean_clauses = set()
        if not parsed_formula:
            return parsed_formula

        operator = parsed_formula[0]
        if operator not in FormulaParser.BOOLEAN_OPS:
            # Base cases: 1. A constant, 2. Only one variable, 3. A non-boolean operator (like "=")
            if (operator not in FormulaParser.BOOLEAN_CONSTANTS) and (parsed_formula not in abstraction):
                # If this is a symmetric operator, make sure that the symmetric formula was not already handled
                symmetric_parsed_formula = FormulaParser.symmetric_formula(parsed_formula)
                if symmetric_parsed_formula in abstraction:
                    return abstraction[symmetric_parsed_formula]
                # Introduce a fresh variable, if this is not a constant
                abstraction[parsed_formula] = str(len(abstraction) + 1)
                non_boolean_clauses.add(parsed_formula)
            return abstraction[parsed_formula]

        left_parameter = FormulaParser._create_boolean_abstraction(parsed_formula[1], signature, abstraction,
                                                                   non_boolean_clauses)
        if operator in FormulaParser.BOOLEAN_UNARY_OPS:
            return operator, left_parameter

        # Binary operator
        right_parameter = FormulaParser._create_boolean_abstraction(parsed_formula[2], signature, abstraction,
                                                                    non_boolean_clauses)
        return operator, left_parameter, right_parameter

    @staticmethod
    def _convert_non_boolean_formulas_to_cnf(signature, parsed_formulas):
        subformulas = {}
        transformed_subformulas = {}
        cnf_formula = set()
        abstraction = {}                # A map between subterms to new variables (the "abstractions")
        non_boolean_clauses = set()     # A set of all non_boolean_clauses
        for parsed_formula in parsed_formulas:
            FormulaParser._convert_to_cnf(
                FormulaParser._create_boolean_abstraction(parsed_formula, signature, abstraction, non_boolean_clauses),
                subformulas=subformulas,
                transformed_subformulas=transformed_subformulas,
                cnf_formula=cnf_formula
            )

        # Keep a mapping of new tseitin variables to original subterms
        tseitin_variable_to_subterm = {}
        subterm_to_tseitin_variable = {}
        for subterm, abstracted_subterm in abstraction.items():
            tseitin_variable_to_subterm[subformulas[abstracted_subterm]] = subterm
            subterm_to_tseitin_variable[subterm] = subformulas[abstracted_subterm]
        return cnf_formula, (tseitin_variable_to_subterm, subterm_to_tseitin_variable), non_boolean_clauses

    @staticmethod
    def import_uf(formula: str):
        signature, parsed_formulas = FormulaParser._parse_uf(formula)
        cnf_formula, (tseitin_variable_to_subterm, subterm_to_tseitin_variable), non_boolean_clauses = \
            FormulaParser._convert_non_boolean_formulas_to_cnf(signature, parsed_formulas)
        congruence_graph = CongruenceGraph(signature, parsed_formulas,
                                           FormulaParser.ALL_OPS, FormulaParser.ALL_BINARY_OPS)
        return (
            frozenset(cnf_formula),
            (tseitin_variable_to_subterm, subterm_to_tseitin_variable),
            (non_boolean_clauses, congruence_graph)
        )
