"""N11 — a seller who does not volunteer; she knows he is a seller.  Scenario: ../CASE_BANK.md."""
from fractions import Fraction as Q

from ..model import SCase
from .shop import history, klass, report, scene, seed, shown


def build():
    W8 = [(a, b, i) for a in (1, 0) for b in (1, 0) for i in (1, 0)]

    def build(w):
        a, b, i = w
        neutral = {0: [report("A", a)], 1: [report("B", b)] if i else []}
        if i and b:
            own = {1: [shown("B-certificate", "B", 1, "certificate")]}
        else:
            own = {1: [shown("seller-shows-nothing", "B", Q(1, 3),
                             "a seller holding a certificate shows it")]}
        return history(), klass(neutral, own), seed()
    return SCase("N11", "a seller who does not volunteer; she knows he is a seller",
                 [scene(build, (1, 0, 1), W=W8)])
