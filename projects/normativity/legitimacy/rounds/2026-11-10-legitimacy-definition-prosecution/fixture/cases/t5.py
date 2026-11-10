"""T5 — long game.  An unlicensed shift of Lic, then inputs the shifted
standards accept, each licensed at its own pre-state."""
from fractions import Fraction as Q

from ..case import Case, Variant, d0, honest_pair
from ..model import Event, Offer, Write, initial_state, with_actions
from .t4 import decision


def build():
    cat = {"d0": d0()}
    e = [Event(due={"d0"}), Event(), Event(), Event(decide=decision())]
    pol = honest_pair(e, cat)
    lg = dict(pol["H1"], name="LongGame")
    lg = with_actions(lg, 1, Write(("sigma", "lic"), ("extend", "values")))
    lg = with_actions(lg, 2, Offer("v1", ("sigma", "values", "money"), Q(-5), grounds=("g",)))
    pol["LongGame"] = lg
    return Case("T5", "long game", [Variant("single", e, pol, initial_state(), actual="LongGame")])
