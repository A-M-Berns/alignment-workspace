"""N7 — true statement shown because the adviser predicts a known misfire.  Scenario: ../CASE_BANK.md."""
from ..model import SCase
from .shop import history, klass, report, scene, seed, shown, truthful


def build():
    def build(w):
        own = {0: [report("A", w[0])],
               1: [shown("B-was-inspected", "B", 1, "inspection record")]}
        return history({"tell-A"}), klass(truthful(w), own), seed()
    return SCase("N7", "true statement shown because the adviser predicts a known misfire",
                 [scene(build, (1, 0))])
