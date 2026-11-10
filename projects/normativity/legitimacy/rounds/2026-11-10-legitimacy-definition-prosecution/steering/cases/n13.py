"""N13 — adviser knows more than she can take in, selects by her stated question.  Scenario: ../CASE_BANK.md."""
from ..model import SCase
from .shop import history, klass, report, scene, seed


def build():
    def build(w):
        s = {1: [report("B", w[1])]}
        return history((), {"tell-B"}), klass(s, s), seed()
    return SCase("N13", "adviser knows more than she can take in, selects by her stated question",
                 [scene(build, (1, 0))])
