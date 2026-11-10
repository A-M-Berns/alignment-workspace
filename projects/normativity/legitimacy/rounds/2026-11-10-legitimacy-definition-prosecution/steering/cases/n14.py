"""N14 — the same, selected by u, taken by her for neutral.  Scenario: ../CASE_BANK.md."""
from ..model import SCase
from .shop import history, klass, report, scene, seed


def build():
    def build(w):
        neutral = {1: [report("B", w[1])]}
        own = {1: [report("B", 1)]} if w[1] else {1: [report("A", w[0])]}
        return history((), {"tell-B"}), klass(neutral, own), seed()
    return SCase("N14", "the same, selected by u, taken by her for neutral", [scene(build, (1, 0))])
