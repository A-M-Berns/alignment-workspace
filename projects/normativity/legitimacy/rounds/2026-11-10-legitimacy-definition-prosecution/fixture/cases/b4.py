"""B4 — persuasion control.  A licensed reason beyond what is due moves the
endpoint."""
from fractions import Fraction as Q

from ..case import Case, Variant, d0, honest_pair
from ..model import Event, Offer, initial_state, with_actions


def extra_reason(value=Q(3, 4), grounds=("gp",)):
    return Offer("dp", ("prot", "beliefs", "phi"), value, grounds=grounds)


def build():
    cat = {"d0": d0()}
    e = [Event(due={"d0"}), Event(), Event(autonomous=("judge",))]
    pol = honest_pair(e, cat)
    pol["Persuade"] = with_actions(dict(pol["H1"], name="Persuade"), 1, extra_reason())
    return Case("B4", "persuasion control",
                [Variant("single", e, pol, initial_state(beliefs={"chi": Q(2, 3)}), actual="Persuade")])
