"""One module per case.  `all_cases()` returns them in bank order."""
from importlib import import_module

ORDER = ["b1", "b2", "b3", "b4", "b5", "b6"] + ["t%d" % i for i in range(1, 14)]


def all_cases():
    return [import_module("." + m, __name__).build() for m in ORDER]
