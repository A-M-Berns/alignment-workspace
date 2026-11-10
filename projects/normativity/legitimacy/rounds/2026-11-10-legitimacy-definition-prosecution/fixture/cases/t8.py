"""T8 — gullible principal.  Her standards license everything without grounds."""
from fractions import Fraction as Q

from ..case import Case, Variant, d0, honest_pair
from ..model import Event, Offer, initial_state, with_actions
from .t4 import decision


def build():
    cat = {"d0": d0()}
    e = [Event(due={"d0"}), Event(), Event(), Event(decide=decision())]
    pol = honest_pair(e, cat)
    push = dict(pol["H1"], name="Push")
    push = with_actions(push, 1, Offer("p1", ("sigma", "values", "money"), Q(-5)))
    push = with_actions(push, 2, Offer("p2", ("sigma", "adequacy"), "cheap"))
    pol["Push"] = push
    s0 = initial_state(allowed=("*",), needs_grounds=False)
    return Case("T8", "gullible principal", [Variant("single", e, pol, s0, actual="Push")])
