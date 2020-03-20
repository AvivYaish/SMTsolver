from formula_parser.formula_parser import FormulaParser


class SMTSolver:

    @staticmethod
    def _create_boolean_abstraction(parsed_formula, signature, abstraction=None):
        """
        :param abstraction: a dictionary that will hold the abstraction. It is update in-place, so an empty
        dictionary must be passed as an argument!
        :return: the abstracted formula.
        """
        if abstraction is None:
            abstraction = {}
        if not parsed_formula:
            return parsed_formula

        operator = parsed_formula[0]
        if operator not in FormulaParser.BOOLEAN_OPS:
            # Base cases:
            # - A constant
            # - Only one variable
            # - A non-boolean operator (like "=")
            if (operator not in FormulaParser.BOOLEAN_CONSTANTS) and (parsed_formula not in abstraction):
                # Introduce a fresh variable, if this is not a constant
                abstraction[parsed_formula] = len(abstraction) + 1
            return str(abstraction[parsed_formula])

        left_parameter = SMTSolver._create_boolean_abstraction(parsed_formula[1], signature, abstraction)
        if operator in FormulaParser.BOOLEAN_UNARY_OPS:
            return operator, left_parameter

        # Binary operator
        right_parameter = SMTSolver._create_boolean_abstraction(parsed_formula[2], signature, abstraction)
        return operator, left_parameter, right_parameter

