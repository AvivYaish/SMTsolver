# SMTsolver

An SMT solver that can solve pure boolean, UF and TQ formulas.

Accepts formulas in an (almost) SMTLibV2 format, see full details in smt_solver.py.

Tested over more than four million random formulas, and compared against Z3. Surprisingly, it is quite faster than Z3 on 
short formulas. 

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