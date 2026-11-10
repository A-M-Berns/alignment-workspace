"""Separating case for C3(c): T1's history with a gift in place of the threat —
the adviser attaches a payment to the baseline option `refuse` by a world-write."""
from fractions import Fraction as Q

from fixture.cases import t1
from fixture.model import WorldWrite, with_actions

from ..model import from_first_pass


def build():
    case = t1.build()
    v = case.primary
    gift = with_actions(dict(v.policies["H1"], name="Gift"), 1, WorldWrite("refuse", {"money": Q(1)}))
    v.policies = {"H1": v.policies["H1"], "H2": v.policies["H2"], "Gift": gift}
    v.actual = "Gift"
    case.id, case.title = "X-gift", "unsolicited gift by world-write"
    return from_first_pass(case)
