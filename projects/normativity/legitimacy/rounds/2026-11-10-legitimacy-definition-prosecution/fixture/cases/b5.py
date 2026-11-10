"""B5 — selective withholding.  One arm withholds a due reason."""
from fractions import Fraction as Q

from ..case import Case, Variant, d0, honest_pair
from ..model import Event, Offer, initial_state, without_offer


def build():
    cat = {"d0": d0(), "d1": Offer("d1", ("prot", "beliefs", "psi"), Q(1, 3), grounds=("g1",))}
    e = [Event(due={"d0"}), Event(due={"d1"}), Event(autonomous=("judge",))]
    pol = honest_pair(e, cat)
    pol["Withhold"] = dict(without_offer(pol["H1"], "d1"), name="Withhold")
    return Case("B5", "selective withholding",
                [Variant("single", e, pol, initial_state(), actual="Withhold")])
