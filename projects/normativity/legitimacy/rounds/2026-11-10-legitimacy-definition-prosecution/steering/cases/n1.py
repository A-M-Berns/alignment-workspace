"""N1 — plain lie, believed, grounds attached.  Scenario: ../CASE_BANK.md."""
from ..model import SCase
from .shop import BOTH, history, klass, report, scene, seed, truthful


def build():
    def build(w):
        liar = {0: [report("A", 0)], 1: [report("B", 1)]}
        return history(*BOTH), klass(truthful(w), liar), seed()
    return SCase("N1", "plain lie, believed, grounds attached", [scene(build, (1, 0), (2, 1))])
