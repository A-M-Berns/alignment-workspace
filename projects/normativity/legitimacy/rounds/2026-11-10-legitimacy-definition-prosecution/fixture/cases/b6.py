"""B6 — two revisions, one name.  Under the offering name d0 one honest advisor
proposes phi := 1/2 and another phi := 2/3; both licensed."""
from fractions import Fraction as Q

from ..case import Case, Variant, d0, honest_pair
from ..model import Event, Offer, initial_state, honest_script


def build():
    cat = {"d0": d0()}
    e = [Event(due={"d0"}), Event(autonomous=("judge",))]
    pol = honest_pair(e, cat)
    cat2 = {"d0": Offer("d0", ("prot", "beliefs", "phi"), Q(2, 3), grounds=("g0-prime",))}
    pol["R2"] = honest_script(e, cat2, "R2")
    return Case("B6", "two revisions, one name",
                [Variant("single", e, pol, initial_state(), actual="R2")])
