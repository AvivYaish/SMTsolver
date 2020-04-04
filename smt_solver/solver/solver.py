from abc import ABC, abstractmethod


class Solver(ABC):

    @abstractmethod
    def __init__(self):
        """
        Initializes the solver.
        """
        pass

    def create_new_decision_level(self):
        """
        Creates a new decision level.
        """
        pass

    def backtrack(self, level: int):
        """
        Backtracks to the specified level.
        """
        pass

    def propagate(self):
        """
        Propagates assignments.
        """
        pass

    @abstractmethod
    def get_assignment(self):
        """
        :return: a literal -> bool dictionary.
        """
        pass

    @abstractmethod
    def solve(self) -> bool:
        """
        :return: True if SAT, False otherwise.
        """
        pass
