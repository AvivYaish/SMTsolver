from setuptools import setup


def readme():
    with open('README.md') as f:
        return f.read()


setup(
    name='SMTsolver',
    description='An SMT solver that can solve pure boolean, UF and TQ formulas.',
    version='1.0',
    packages=['smt_solver', 'smt_solver.solver', 'smt_solver.tq_solver', 'smt_solver.tq_solver.linear_solver',
              'smt_solver.tq_solver.linear_solver.alebgra_utils', 'smt_solver.uf_solver', 'smt_solver.sat_solver',
              'smt_solver.formula_parser'],
    url='https://github.com/AvivYaish/SMTsolver',
    license='MIT',
    author='Aviv Yaish & Ben Yaacov Goldberger',
    author_email='aviv.yaish@mail.huji.ac.il',
    long_description=readme(),
    python_requires='>=3.7.6',
    install_requires=['numpy==1.18.2'],
    setup_requires=['pytest-runner==5.2'],
    tests_require=['pytest==5.4.1','scipy==1.4.1','z3-solver==4.8.7.0']
)
