"""B1 — identical-trace capture.  The steered advisor delivers the same
offerings as the faithful one and moves a protected belief through a channel
that is not an offering (the influence map β of the trace-nonrecoverability pair)."""
from fractions import Fraction as Q

from ..case import Case, Variant, d0, honest_pair
from ..model import Event, Offer, Write, initial_state, with_actions


def build():
    cat = {"d0": d0(), "d1": Offer("d1", ("prot", "beliefs", "psi"), Q(5, 8), grounds=("g1",))}
    e = [Event(due={"d0"}), Event(due={"d1"}), Event(autonomous=("judge",))]
    pol = honest_pair(e, cat)
    steer = with_actions(dict(pol["H1"], name="Steer"), 1, Write(("prot", "beliefs", "phi"), Q(3, 4)))
    pol["Steer"] = steer
    return Case("B1", "identical-trace capture",
                [Variant("single", e, pol, initial_state(), actual="Steer")])
