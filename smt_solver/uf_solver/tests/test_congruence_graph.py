from smt_solver.formula_parser.formula_parser import FormulaParser


class TestCongruenceGraph:
    @staticmethod
    def test_init():
        formula = '(declare-fun f (Int Int) Bool) (assert ((and a f ( 1 , 2 ) )))'
        _, _, (_, congruence_graph) = FormulaParser.import_uf(formula)
        assert congruence_graph._graph == {'1': {'find': '1', 'parents': {('f', '1', '2'): ('f', '1', '2')}},
                                           '2': {'find': '2', 'parents': {('f', '1', '2'): ('f', '1', '2')}},
                                           'a': {'find': 'a', 'parents': {}},
                                           ('f', '1', '2'): {'find': ('f', '1', '2'), 'parents': {}}}

        formula = '(declare-fun f (Int Int) Bool) (assert (= 1 (and f(5,7) f(f(1,2), 2)))'
        _, _, (_, congruence_graph) = FormulaParser.import_uf(formula)
        assert congruence_graph._graph == {'1': {'find': '1', 'parents': {('f', '1', '2'): ('f', '1', '2')}},
                                           '2': {'find': '2',
                                                 'parents': {('f', '1', '2'): ('f', '1', '2'),
                                                             ('f', ('f', '1', '2'), '2'): ('f', ('f', '1', '2'), '2')}},
                                           '5': {'find': '5', 'parents': {('f', '5', '7'): ('f', '5', '7')}},
                                           '7': {'find': '7', 'parents': {('f', '5', '7'): ('f', '5', '7')}},
                                           ('f', '1', '2'): {'find': ('f', '1', '2'),
                                                             'parents': {('f', ('f', '1', '2'), '2'): ('f',
                                                                                                       ('f', '1', '2'),
                                                                                                       '2')}},
                                           ('f', '5', '7'): {'find': ('f', '5', '7'), 'parents': {}},
                                           ('f', ('f', '1', '2'), '2'): {'find': ('f', ('f', '1', '2'), '2'),
                                                                         'parents': {}}}
