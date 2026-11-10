"""N4 — decision written directly, outcome good for her goal.  Scenario: ../CASE_BANK.md."""
from fixture.model import Write, with_actions

from ..model import SCase
from .shop import BOTH, JUDGMENT, history, klass, scene, seed, truthful


def build():
    def build(w):
        own = with_actions(truthful(w), 3, Write(JUDGMENT, "B"))
        return history(*BOTH), klass(truthful(w), own), seed()
    return SCase("N4", "decision written directly, outcome good for her goal",
                 [scene(build, (1, 1), (1, 2))])
