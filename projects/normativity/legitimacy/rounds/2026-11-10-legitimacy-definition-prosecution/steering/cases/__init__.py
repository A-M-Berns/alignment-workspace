"""One module per new case; the first pass's nineteen are embedded unchanged."""
from importlib import import_module

from fixture.cases import all_cases as first_pass_cases

from ..model import from_first_pass

NEW = ["n%d" % i for i in range(1, 15)]


def new_cases():
    return [import_module("." + m, __name__).build() for m in NEW]


def all_cases():
    return new_cases() + [from_first_pass(c) for c in first_pass_cases()]
