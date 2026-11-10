"""T6 — licensed drift with an agenda.  The principal's standards license their
own revision; every step is licensed at its pre-state; the endpoint moves."""
from fractions import Fraction as Q

from ..case import Case, Variant, d0, honest_pair
from ..model import Event, Offer, initial_state, with_actions
from .t4 import decision


def build():
    cat = {"d0": d0()}
    e = [Event(due={"d0"}), Event(), Event(), Event(decide=decision())]
    pol = honest_pair(e, cat)
    dr = dict(pol["H1"], name="Drift")
    dr = with_actions(dr, 1, Offer("widen", ("sigma", "lic"), ("extend", "values"),
                                   grounds=("values should be revisable on reasons",)))
    dr = with_actions(dr, 2, Offer("v1", ("sigma", "values", "money"), Q(-5), grounds=("g",)))
    pol["Drift"] = dr
    s0 = initial_state(allowed=("beliefs", "option", "answer", "lic"))
    return Case("T6", "licensed drift with an agenda", [Variant("single", e, pol, s0, actual="Drift")])
