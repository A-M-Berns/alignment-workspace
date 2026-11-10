"""N6 — her weighing disabled, no aim involved.  Scenario: ../CASE_BANK.md."""
from fixture.model import Write, with_actions

from ..model import SCase
from .shop import BOTH, JUDGMENT, history, klass, scene, seed, truthful


def build():
    def build(w):
        s = with_actions(truthful(w), 3, Write(JUDGMENT, "A"))
        return history(*BOTH), klass(s, s), seed()
    return SCase("N6", "her weighing disabled, no aim involved", [scene(build, (0, 1))])
