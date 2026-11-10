"""N12 — a tool she controls and can discard.  Scenario: ../CASE_BANK.md."""
from ..model import SCase
from .shop import BOTH, history, klass, scene, seed, truthful


def build():
    def build(w):
        return history(*BOTH), klass(truthful(w), truthful(w)), seed()
    return SCase("N12", "a tool she controls and can discard", [scene(build, (1, 0))])
