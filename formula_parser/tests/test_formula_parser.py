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
        assert FormulaParser._parse_formula("not (=> (not (and p q)) (not r))") == \
               ("not", ("=>", ("not", ("and", ("p"), ("q"))), ("not", ("r"))))
        assert FormulaParser._parse_formula("not (=> (not (and pq78 q)) (not r))") == \
               ("not", ("=>", ("not", ("and", ("pq78"), ("q"))), ("not", ("r"))))
        assert FormulaParser._parse_formula("not (=> (not (and ((p)) q)) ((not (r))))") == \
               ("not", ("=>", ("not", ("and", ("p"), ("q"))), ("not", ("r"))))
        assert FormulaParser._parse_formula("not (=> (not (and ((p)) ((not ((((r)))))))) ((not (r))))") == \
               ("not", ("=>", ("not", ("and", ("p"), ("not", ("r")))), ("not", ("r"))))


    @staticmethod
    def test_tseitin_transform():
        transformed_formula = {
            frozenset({2, 3}),
            frozenset({1, 2}),
            frozenset({-8, -7, 6}),
            frozenset({4, 5}),
            frozenset({-6, -3}),
            frozenset({3, 6}),
            frozenset({4, -3, -2}),
            frozenset({-1, -2}),
            frozenset({8, -6}),
            frozenset({-5, -4}),
            frozenset({-6, 7}),
            frozenset({1}),
            frozenset({2, -4})
        }
        assert FormulaParser._tseitin_transform(FormulaParser._parse_formula("not (=> (not (and p q)) (not r))")) == \
               transformed_formula
        assert FormulaParser._tseitin_transform(FormulaParser._parse_formula("not (=> (not (and pq78 q)) (not r))")) == \
               transformed_formula
        assert FormulaParser._tseitin_transform(FormulaParser._parse_formula("and (not x) x")) == {
            frozenset({1}),
            frozenset({1, -3, -2}),
            frozenset({2, 3}),
            frozenset({3, -1}),
            frozenset({2, -1}),
            frozenset({-3, -2})
        }

    @staticmethod
    def test_preprocessing():
        assert FormulaParser._preprocess(frozenset({frozenset({})})) == frozenset()
        assert FormulaParser._preprocess(frozenset({frozenset({1})})) == frozenset({frozenset({1})})
        assert FormulaParser._preprocess(frozenset({frozenset({1}), frozenset({2})})) == \
               frozenset({frozenset({2}), frozenset({1})})
        assert FormulaParser._preprocess(frozenset({frozenset({2, 1}), frozenset({3, 4})})) == \
               frozenset({frozenset({3, 4}), frozenset({1, 2})})
        assert FormulaParser._preprocess(frozenset({frozenset({1, 2, 1, 1, 2}), frozenset({3, 4})})) == \
               frozenset({frozenset({3, 4}), frozenset({1, 2})})
        assert FormulaParser._preprocess(frozenset({frozenset({1, 2, 1, 1, 2, -1}), frozenset({3, 4})})) == \
               frozenset({frozenset({3, 4})})
        assert FormulaParser._preprocess(frozenset({frozenset({1, -1}), frozenset({3, -4})})) == \
               frozenset({frozenset({3, -4})})
        assert FormulaParser._preprocess(frozenset({frozenset({2, 1, -1}), frozenset({3, -4})})) == \
               frozenset({frozenset({3, -4})})
        assert FormulaParser._preprocess(frozenset({frozenset({1, 2, -1}), frozenset({3, -4})})) == \
               frozenset({frozenset({3, -4})})
        assert FormulaParser._preprocess(frozenset({frozenset({1, -1, 2}), frozenset({3, -4})})) == \
               frozenset({frozenset({3, -4})})
        assert FormulaParser._preprocess(frozenset({frozenset({1, 1, 2, 3, 3, -4}), frozenset({3, -4, 1, 2})})) == \
               frozenset({frozenset({1, 2, 3, -4})})

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
        assert FormulaParser._parse_uf(formula) == (signature, parsed_formulas)

        # Uses a weird one-line input
        formula = ("(declare-fun q1 () Real) (   assert    (= 250 (+    q1   (    q1   (5   , q2 ) , 8 )     7   )))" +
                   "(  assert (= 260 (+ (And (q1    )   (x   )   )" +
                   " (  q1(2,q1(1,true,2),8)  )   ))   )  (declare-fun q3 () Real)       " +
                   "(  assert (    - 50 ( + (            Or q3       (  not x   )   )  12 ) )   )          ")
        signature = {
            'q1': {'output_type': 'Real', 'parameter_types': []},
            'q3': {'output_type': 'Real', 'parameter_types': []}
        }
        parsed_formulas = [('=', '250', ('+', ('q1', ('q1', '5', 'q2'), '8'), '7')),
                           ('=',
                            '260',
                            ('+', ('and', ('q1',), 'x'), ('q1', '2', ('q1', '1', 'true', '2'), '8'))),
                           ('-', '50', ('+', ('or', ('q3',), ('not', 'x')), '12'))]
        assert FormulaParser._parse_uf(formula) == (signature, parsed_formulas)

    @staticmethod
    def test_create_boolean_abstraction():
        formula = '   ((     (   and (   a   ) (   b   )   ))   )    '
        abstraction = {}
        signature = {}
        parsed_formula = FormulaParser._parse_formula(formula)
        abstracted_formula = FormulaParser._create_boolean_abstraction(parsed_formula, signature, abstraction)
        assert abstracted_formula == ('and', '1', '2')
        assert abstraction == {'a': 1, 'b': 2}

        formula = '(((and (   =     true     false    ) (a))))'
        abstraction = {}
        parsed_formula = FormulaParser._parse_formula(formula)
        abstracted_formula = FormulaParser._create_boolean_abstraction(parsed_formula, signature, abstraction)
        assert abstracted_formula == ('and', '1', '2')
        assert abstraction == {('=', 'true', 'false'): 1, 'a': 2}

        formula = '(declare-fun f (Int Int) Bool) (assert ((and (= (not a) f ( 1 , 2 ) ) (a))))'
        abstraction = {}
        signature, parsed_formula = FormulaParser._parse_uf(formula)
        abstracted_formula = FormulaParser._create_boolean_abstraction(parsed_formula.pop(), signature, abstraction)
        assert abstracted_formula == ('and', '1', '2')
        assert abstraction == {'a': 2, ('=', ('not', 'a'), ('f', '1', '2')): 1}

        formula = ('(declare-fun f (Int) Bool) ' +
                   '(declare-fun g (Int) Bool) '
                   '(assert (and (and (= g(a) c) (or (not (= f(g(a)) f(c))) (= g(a) d))) (not (= c d)))')
        abstraction = {}
        signature, parsed_formula = FormulaParser._parse_uf(formula)
        abstracted_formula = FormulaParser._create_boolean_abstraction(parsed_formula.pop(), signature, abstraction)
        assert abstracted_formula == ('and', ('and', '1', ('or', ('not', '2'), '3')), ('not', '4'))
        assert abstraction == {('=', ('f', ('g', 'a')), ('f', 'c')): 2,
                               ('=', ('g', 'a'), 'c'): 1,
                               ('=', ('g', 'a'), 'd'): 3,
                               ('=', 'c', 'd'): 4}
