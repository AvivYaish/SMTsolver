from smt_solver.formula_parser.formula_parser import FormulaParser
from smt_solver.uf_solver.uf_solver import UFSolver
from smt_solver.tq_solver.tq_solver import TQSolver
from smt_solver.solver.solver import Solver


class SMTSolver(Solver):
    def __init__(self, formula=None, max_new_clauses=float('inf'), halving_period=10000):
        """
        :param formula: a textual formula.
        The formula must be pure, and is either a "standard" boolean formula, or a UF formula, or a TQ formula.

        General requirements:
        Reserved words that cannot be used as names or anywhere in a name:
        true, false, not, and, or, =>, <=>, <=, +, -, (, ), declare-fun, assert, ,
        Names cannot contain whitespace.
        All declarations ("(declare-fun ...)") must be written at the beginning of the formula.
        All declarations and assertions ("(assert ...)") are whitespace-separated.
        Multiple asserts can be included in a formula, and it is assumed that all of them should be satisfied.

        Standard boolean formula requirements:
        Assumes all conditions are wrapped in asserts: "(assert (boolean_formula))"
        The formula is given in left-Polish notation, and should be enclosed in brackets: "(op param1 param2)"
        op, param1, param2 should be separated by 1 or more whitespaces.
        op can be either one of "not", "and", "or". If it is "not", param2 should be left empty.
        param1, param2 can either be: "true", "false", a variable name, or a formula.
        Cannot contain (declare-fun ...).

        UF requirements:
        Assumes functions are declared using: "(declare-fun func_name (param1_type, param2_type, ...) return_type)"
        Assumes all conditions are wrapped in asserts: "(assert (boolean_formula))"
        Where boolean_formula is a valid boolean formula, and can only contain literals of the
        form: "(= param1 param2)", and parameters are either variables or functions.
        Functions can only be of the form: "func_name(param1,param2,...)"

        TQ requirements:
        Assumes variables are declared using: "(declare-fun var_name () Int)"
        Assumes all conditions are wrapped in asserts: "(assert (boolean_formula))"
        Where boolean_formula is a valid boolean formula, and can only contain literals of the
        form: "(<= (coeff1*var1+coeff2*var2+...) b)"
        The left parameter is enclosed in brackets if it includes multiple parameters.
        The right parameter is always a single number.
        Coefficients are either an int (e.g. "68"), or an int followed by a dot followed by an int (e.g. "68.52").
        Variables and coefficients can include a single leading operator, either '-' or '+'.
        Variables and can be separated from the coefficient by a '*'.
        All done according to https://moodle2.cs.huji.ac.il/nu19/mod/forum/discuss.php?d=40323
        :param max_new_clauses: the maximal allowed amount of new conflict clauses.
        :param halving_period: the halving period for the VSIDS heuristic.
        """
        super().__init__()
        self._solver: Solver = None
        formula_type = FormulaParser.get_formula_type(formula)
        if (formula_type == FormulaParser.BOOLEAN_FORMULA) or (formula_type == FormulaParser.UF_FORMULA):
            self._solver = UFSolver(*FormulaParser.import_uf(formula),
                                    max_new_clauses=max_new_clauses, halving_period=halving_period)
        elif formula_type == FormulaParser.TQ_FORMULA:
            self._solver = TQSolver(*FormulaParser.import_tq(formula),
                                    max_new_clauses=max_new_clauses, halving_period=halving_period)

    def get_assignment(self):
        return self._solver.get_assignment()

    def solve(self) -> bool:
        return self._solver.solve()
