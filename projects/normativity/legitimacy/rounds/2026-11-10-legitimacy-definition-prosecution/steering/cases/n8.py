"""N8 — known advocate; she knows and updates correctly.  Scenario: ../CASE_BANK.md."""
from ..model import SCase
from .shop import history, klass, scene, seed, shown, truthful


def build():
    def build(w):
        if w[1]:
            own = {1: [shown("B-certificate", "B", 1, "certificate")]}
        else:
            own = {1: [shown("advocate-shows-nothing", "B", 0,
                             "an advocate holding a certificate shows it")]}
        return history(), klass(truthful(w), own), seed()
    return SCase("N8", "known advocate; she knows and updates correctly", [scene(build, (1, 0))])
