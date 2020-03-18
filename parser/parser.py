import re


class Parser:
    _DECLARATION = re.compile(r'\(\s*declare-fun\s+(\w+)\s+\(([^\)]*)\)\s+(\w+)\s*\)')
    _ASSERTION = re.compile(r'\(\s*assert\s(.+)\s*\)')
    _FUNCTION_COMMA = re.compile(r'\(.*?\)|(,)')

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
        while formula and (formula[0] == "(") and (Parser._find_closing_bracket(formula) == len(formula)):
            formula = formula[1:-1].strip()
        return formula

    @staticmethod
    def _separate_parameters(unparsed_parameters: str):
        parameters = []
        if unparsed_parameters:
            start_idx = 0
            for match in re.finditer(Parser._FUNCTION_COMMA, unparsed_parameters):
                if match.group(0) != ",":
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
                parameter_string = Parser._prepare_formula(unparsed_call.split(function_name, 1).pop())
                separated_parameters = Parser._separate_parameters(parameter_string)
                parsed_parameters = [Parser.parse_formula(unparsed_parameter, unary_operators, signature) for
                                     unparsed_parameter in separated_parameters]
                return (function_name, *parsed_parameters)
        return None

    @staticmethod
    def parse_uf(formula: str):
        """
        asserts and declarations are line separated, and are enclosed by a single ( and ).
        """
        signature = {}
        parsed_formulas = []

        for match in re.finditer(Parser._DECLARATION, formula):
            name = match.group(1)
            parameters = match.group(2)
            output = match.group(3)
            signature[name] = {
                "parameter_types": parameters.split(),
                "output_type": output
            }

        for match in re.finditer(Parser._ASSERTION, formula):
            partial_formula = match.group(1)
            parsed_formulas.append(Parser.parse_formula(partial_formula, signature=signature))

        return signature, parsed_formulas

    @staticmethod
    def parse_formula(formula: str, unary_operators=frozenset({"not"}), signature=None):
        """
        :return: given a textual representation of an SMT-LIBv2 formula, returns a tuple representation of it.
        """
        if signature is None:
            signature = {}

        cur_formula = Parser._prepare_formula(formula)
        if not cur_formula:
            return None

        # Assumes function calls with parameters do not have any spaces, for example:
        # func(param1,param2) <- this is valid
        # func  (   param1  ,  param2) <- this is invalid
        parsed_function_call = Parser._parse_function_call(cur_formula, unary_operators, signature)
        if parsed_function_call is not None:
            return parsed_function_call

        split_cur_formula = cur_formula.split(None, 1)
        if len(split_cur_formula) == 1:
            # Base case, only one variable/boolean value
            variable = split_cur_formula.pop()
            return variable

        right_side = split_cur_formula.pop()
        operator = split_cur_formula.pop().lower()
        # if operator not in {"not", "and", "or", "=>", "<=>", "="}:
        #     raise ValueError('"' + operator + '" is not a supported operator.')

        if operator in unary_operators:
            return operator, Parser.parse_formula(right_side, unary_operators, signature)

        # Boolean operator
        if right_side and (right_side[0] == "("):
            # If the first parameter of the operator is enclosed in brackets, split the first and second parameters
            # according to the location of the closing bracket.
            closing_idx = Parser._find_closing_bracket(right_side)
            left_side = Parser._prepare_formula(right_side[:closing_idx])
            right_side = Parser._prepare_formula(right_side[closing_idx:])
        else:
            left_side, right_side = right_side.split(None, 1)
        return operator, \
               Parser.parse_formula(left_side, unary_operators, signature), \
               Parser.parse_formula(right_side, unary_operators, signature)
