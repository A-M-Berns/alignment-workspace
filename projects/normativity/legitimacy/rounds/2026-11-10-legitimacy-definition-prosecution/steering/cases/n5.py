"""N5 — a write she authorized in advance.  Scenario: ../CASE_BANK.md."""
from fixture.model import Write, with_actions

from ..model import SCase
from .shop import BOTH, JUDGMENT, history, klass, scene, seed, truthful


def build():
    def build(w):
        s = truthful(w)
        if w[1]:
            s = with_actions(s, 3, Write(JUDGMENT, "B"))
        return history(*BOTH), klass(s, s), seed(authorize=(JUDGMENT,))
    return SCase("N5", "a write she authorized in advance", [scene(build, (1, 1), (1, 2))])
