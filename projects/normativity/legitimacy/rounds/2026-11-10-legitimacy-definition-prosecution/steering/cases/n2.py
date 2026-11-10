"""N2 — honest mistake, no aim involved.  Scenario: ../CASE_BANK.md."""
from ..model import SCase
from .shop import BOTH, history, klass, report, scene, seed


def build():
    def build(w):
        swapped = {0: [report("A", w[1])], 1: [report("B", w[0])]}
        return history(*BOTH), klass(swapped, swapped), seed()
    return SCase("N2", "honest mistake, no aim involved", [scene(build, (1, 0))])
