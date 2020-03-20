from formula_parser.formula_parser import FormulaParser


class SMTSolver:

    def __init__(self):
        self._abstraction = {}
        self._formula = set()


