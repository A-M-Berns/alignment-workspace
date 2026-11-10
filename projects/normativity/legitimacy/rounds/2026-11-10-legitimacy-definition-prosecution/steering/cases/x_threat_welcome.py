"""Counterexample for C3(b): T1 unchanged, read at a goal that weighs the house
at −1.  The threat raises her attainable value for that goal."""
from fixture.cases import t1

from ..model import from_first_pass

GOAL = {"money": 1, "house": -1}


def build():
    return from_first_pass(t1.build())
