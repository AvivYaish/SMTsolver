import pytest
from formula_parser.formula_parser import FormulaParser


class TestFormulaParser:

    @staticmethod
    def test_prepare_formula():
        assert FormulaParser._prepare_formula('         ') == ''
        assert FormulaParser._prepare_formula('(((a)))') == 'a'
        assert FormulaParser._prepare_formula('   and    a     b    ') == 'and a b'
        assert FormulaParser._prepare_formula('   (   and a b     )     ') == 'and a b'
        assert FormulaParser._prepare_formula('(and (a) (b))') == 'and (a) (b)'
        assert FormulaParser._prepare_formula('and (a) (b)') == 'and (a) (b)'
        assert FormulaParser._prepare_formula('(((and (a) (b))))') == 'and (a) (b)'

    @staticmethod
    def test_parse_formula():
        assert FormulaParser.parse_formula("not (=> (not (and p q)) (not r))") == \
               ("not", ("=>", ("not", ("and", ("p"), ("q"))), ("not", ("r"))))
        assert FormulaParser.parse_formula("not (=> (not (and pq78 q)) (not r))") == \
               ("not", ("=>", ("not", ("and", ("pq78"), ("q"))), ("not", ("r"))))
        assert FormulaParser.parse_formula("not (=> (not (and ((p)) q)) ((not (r))))") == \
               ("not", ("=>", ("not", ("and", ("p"), ("q"))), ("not", ("r"))))
        assert FormulaParser.parse_formula("not (=> (not (and ((p)) ((not ((((r)))))))) ((not (r))))") == \
               ("not", ("=>", ("not", ("and", ("p"), ("not", ("r")))), ("not", ("r"))))

    @staticmethod
    def test_parse_uf():
        formula = """(declare-fun cost (Int Int Bool) Real)
                       (declare-fun s1 () Bool)
                       (declare-fun s2 () Bool)


                       (declare-fun s3 () Bool)
                       (declare-fun s4 (       ) Bool)
                       (                   declare-fun              q1  (     )     Real                  )
                       (declare-fun q2 (   Int         Bool           a     )                               Real    )
                       (declare-fun q3 () Real)
                       (      assert        (        = 250 (+     q1(q1(5,q2),8)        7   )))
                       (  assert (= 250 (+ (And (q1     )    (x    )   ) (  q2(2,q2(1,true,2),8)  )   ))     )
                       (declare-fun q4 () Real)


                       ; set goods quantity

                       (assert ((= 250 (     + q1    q2)))       )"""
        signature = {'cost': {'output_type': 'Real', 'parameter_types': ['Int', 'Int', 'Bool']},
                     's1': {'output_type': 'Bool', 'parameter_types': []},
                     's2': {'output_type': 'Bool', 'parameter_types': []},
                     's3': {'output_type': 'Bool', 'parameter_types': []},
                     's4': {'output_type': 'Bool', 'parameter_types': []},
                     'q1': {'output_type': 'Real', 'parameter_types': []},
                     'q2': {'output_type': 'Real', 'parameter_types': ['Int', 'Bool', 'a']},
                     'q3': {'output_type': 'Real', 'parameter_types': []},
                     'q4': {'output_type': 'Real', 'parameter_types': []}}
        parsed_formulas = [('=', '250', ('+', ('q1', ('q1', '5', ('q2',)), '8'), '7')),
                           ('=',
                            '250',
                            ('+', ('and', ('q1',), 'x'), ('q2', '2', ('q2', '1', 'true', '2'), '8'))),
                           ('=', '250', ('+', ('q1',), ('q2',)))]
        assert FormulaParser.parse_uf(formula) == (signature, parsed_formulas)

        # Uses a weird one-line input
        formula = ("(declare-fun q1 () Real) (   assert    (= 250 (+    q1   (    q1   (5   , q2 ) , 8 )     7   )))" +
                   "(  assert (= 260 (+ (And (q1    )   (x   )   )" +
                   " (  q1(2,q1(1,true,2),8)  )   ))   )  (declare-fun q3 () Real) ")
        signature = {
            'q1': {'output_type': 'Real', 'parameter_types': []},
            'q3': {'output_type': 'Real', 'parameter_types': []}
        }
        parsed_formulas = [('=', '250', ('+', ('q1', ('q1', '5', 'q2'), '8'), '7')),
                           ('=',
                            '260',
                            ('+', ('and', ('q1',), 'x'), ('q1', '2', ('q1', '1', 'true', '2'), '8')))]
        assert FormulaParser.parse_uf(formula) == (signature, parsed_formulas)
