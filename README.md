# SMTsolver

An SMT solver that can solve pure boolean, UF and TQ formulas.

Accepts formulas in an (almost) SMT-LIBv2 format, see full details below.

Tested and compared against Z3 over more than four million random formulas. Surprisingly, it is quite faster than Z3 on 
short formulas (tens of thousands of clauses long). When receiving complex formulas as inputs, the solver still holds 
its ground: it can solve a randomly generated formula with 20 million operators (Not, And, Or, =>, <=>) and 100,000 
literals in a few minutes.

### Installation
Download the repository and run: 

        cd SMTSolver
        pip install .
        
### Usage
1. Create a new SMTSolver with a textual formula:
        
        
        solver = SMTSolver("(declare-fun f (Int) Int) (assert (= f(x) f(y))) (assert (not (= x y)))")


2. Solve the formula:
        
        
        solver.solve()

3. Get the assignment:


        solver.get_assignment()
        
### Formula format
The formula must be pure, either a "standard" boolean formula, or a UF formula, or a TQ formula.

##### General requirements
- Reserved words that cannot be used as names or anywhere in a name:
true, false, not, and, or, =>, <=>, <=, +, -, (, ), declare-fun, assert, ,
- Names cannot contain whitespace.
- All declarations ("(declare-fun ...)") must be written at the beginning of the formula.
- All declarations and assertions ("(assert ...)") are whitespace-separated.
Multiple asserts can be included in a formula, and it is assumed that all of them should be satisfied.

##### Standard boolean formula requirements
- Assumes all conditions are wrapped in asserts: "(assert (boolean_formula))"
- The formula is given in left-Polish notation, and should be enclosed in brackets: "(op param1 param2)"
- op, param1, param2 should be separated by 1 or more whitespaces.
- op can be either one of "not", "and", "or", "=>", "<=>". If it is "not", param2 should be left empty.
- param1, param2 can either be: "true", "false", a variable name, or a formula.
- Cannot contain (declare-fun ...).

##### UF requirements
- Assumes functions are declared using: "(declare-fun func_name (param1_type, param2_type, ...) return_type)"
- Assumes all conditions are wrapped in asserts: "(assert (boolean_formula))", where boolean_formula is a 
valid boolean formula, and can only contain literals of the form: "(= param1 param2)", and parameters are 
either variables or functions. 
- Functions can only be of the form: "func_name(param1,param2,...)"

##### TQ requirements
- Assumes variables are declared using: "(declare-fun var_name () Int)"
- Assumes all conditions are wrapped in asserts: "(assert (boolean_formula))", where boolean_formula is a 
valid boolean formula, and can only contain literals of the form: "(<= (coeff1*var1+coeff2*var2+...) b)"
- The left parameter is enclosed in brackets if it includes multiple parameters.
- The right parameter is always a single number.
- Coefficients are either an int (e.g. "68"), or an int followed by a dot followed by an int (e.g. "68.52").
- Variable names must start with a letter.
- Variables and coefficients can include a single leading operator, either '-' or '+'.
- Variables and can be separated from the coefficient by a '*'.
- All done according to https://moodle2.cs.huji.ac.il/nu19/mod/forum/discuss.php?d=40323

### Technical details
##### FormulaParser
- Simplifies formulas: 1. Removes doubles Nots: Not (Not ...), 2. (And x x) = (Or x x) = x, 3. MUCH much more! 
See FormulaParser._simplify_formula for all details 
- Converts to CNF using Tseitin's transform. The transform does not create new variables for "not" or for identical
subformulas.
- Preprocesses CNF clauses to remove redundant literals, trivial clauses, and multiple identical clauses. 

##### SATSolver
Uses:
- Unit propagation.
- Case splitting, with non-chronological backtracking.
- The VSIDS heuristic. 
- Watch-clauses. 
- Conflict clause learning and analysis using implication graphs, with the Unique Implication Point heuristic.

##### UFSolver
- Checks partial and satisfying assignments to determine T-satisfiability.
- Reports T-conflicts to the SAT solver and performs T-propagations.
- Performs the congruence-closure algorithm, supports functions with multiple arguments.

##### TQSolver
Uses LinearSolver, an LP solver that implements the following: 
- Revised-simplex, which uses eta matrices, LU decomposition and checks numerical stability.
- Supports auxiliary problems.
- Implements Bland's and Dantzig's selection rules.

##### SMTSolver
Unifies all above solvers, and picks the correct one according to the input formula.

##### Tests
- Uses all homework assignments.
- Uses randomly generated formulas.
- We have noticed that most run-time is spent simply generating the random tests, so
fast numpy code was used to speed this up. Still, generation is the most time-consuming task. 

### Possible improvements
- Multithreading - using multiple heuristics + multiple "dumb" brute-force searches (each covering a different part of 
the search space) to preemptively find conflict clauses. When a new clause is found, every search that conflicts on it
performs a back-jump.
