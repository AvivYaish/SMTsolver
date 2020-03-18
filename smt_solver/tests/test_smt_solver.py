import pytest
from smt_solver.smt_solver import SMTSolver


class TestSMTSolver:

    @staticmethod
    def test_parse_formula_uf():
        formula = """(declare-fun cost (Int Int Bool) Real)
                        (declare-fun s1 () Bool)
                        (declare-fun s2 () Bool)
                        
                        
                        (declare-fun s3 () Bool)
                        (declare-fun s4 (       ) Bool)
                        (                   declare-fun              q1      (     )     Real                  )
                        (declare-fun q2 (   Int         Bool           a     )                               Real    )
                        (declare-fun q3 () Real)
                        (            assert           (        = 250 (+           q1                       q2   q3 q4)))
                        (  assert (= 250 (+ (And (q1         )         (x    )   )     q2     q3 q4      ))     )
                        (declare-fun q4 () Real)
                        
                        
                        ; set goods quantity
                        
                        (assert ((= 250 (     + q1 q2 q3 q4)))       )"""
        signature = {'cost': {'output_type': 'Real', 'parameter_types': ['Int', 'Int', 'Bool']},
                     's1': {'output_type': 'Bool', 'parameter_types': []},
                     's2': {'output_type': 'Bool', 'parameter_types': []},
                     's3': {'output_type': 'Bool', 'parameter_types': []},
                     's4': {'output_type': 'Bool', 'parameter_types': []},
                     'q1': {'output_type': 'Real', 'parameter_types': []},
                     'q2': {'output_type': 'Real', 'parameter_types': ['Int', 'Bool', 'a']},
                     'q3': {'output_type': 'Real', 'parameter_types': []},
                     'q4': {'output_type': 'Real', 'parameter_types': []}}
        parsed_formulas = ['= 250 (+ q1 q2 q3 q4)', '= 250 (+ (And (q1 ) (x ) ) q2 q3 q4 )', '= 250 ( + q1 q2 q3 q4)']
        assert signature, parsed_formulas == SATSolver._parse_formula_uf(formula)
