import re


class FormulaParser:
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
    ALL_OPS = UF_OPS | BOOLEAN_OPS

    _OPENING_BRACKET = '('
    _CLOSING_BRACKET = ')'
    _PARAMETER_SEPARATOR = ','

    _DECLARATION = re.compile(r'\(\s*declare-fun\s+(\w+)\s+\(([^\)]*)\)\s+(\w+)\s*\)')
    _ASSERTION = re.compile(r'\(\s*assert\s*')
    _FUNCTION_COMMA = re.compile(r'\(.*?\)|(,)')

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
                parsed_parameters = [FormulaParser.parse_formula(unparsed_parameter, unary_operators, signature) for
                                     unparsed_parameter in separated_parameters]
                return (function_name, *parsed_parameters)
        return None

    @staticmethod
    def parse_uf(formula: str, unary_operators=BOOLEAN_UNARY_OPS):
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
            parsed_formulas.append(FormulaParser.parse_formula(unparsed_formula, unary_operators, signature))

        return signature, parsed_formulas

    @staticmethod
    def parse_formula(formula: str, unary_operators=BOOLEAN_UNARY_OPS, signature=None):
        """
        :return: given a textual representation of an SMT-LIBv2 formula, returns a tuple representation of it.
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
            return operator, FormulaParser.parse_formula(right_side, unary_operators, signature)

        # Boolean operator
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
        return operator, \
               FormulaParser.parse_formula(left_side, unary_operators, signature), \
               FormulaParser.parse_formula(right_side, unary_operators, signature)
