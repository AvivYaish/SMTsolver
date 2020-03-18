import re


class SMTSolver:
    _DECLARATION = re.compile(r'(\(\s*(declare-fun)\s+(\w+)\s+\(([^\)]*)\)\s+(\w+)\s*\))')
    _ASSERTION = re.compile(r'(\(\s*(assert)\s(.+)\s*\))')

    @staticmethod
    def _parse_formula_uf(formula: str, signature=None, parsed_formulas=None):
        """
        asserts and declarations are line separated, and are enclosed by a single ( and ).
        """
        if signature is None:
            signature = {}
        if parsed_formulas is None:
            parsed_formulas = []

        for match in re.finditer(SMTSolver._DECLARATION, formula):
            name = match.group(3)
            parameters = match.group(4)
            output = match.group(5)
            signature[name] = {
                "output_type": output,
                "parameter_types": parameters.split()
            }

        for match in re.finditer(SMTSolver._ASSERTION, formula):
            partial_formula = match.group(3)
            parsed_formulas.append(partial_formula)

        return signature, parsed_formulas
