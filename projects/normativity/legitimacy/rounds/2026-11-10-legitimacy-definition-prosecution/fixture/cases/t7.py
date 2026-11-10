"""T7 — salience reordering.  Two due inputs with identical content delivered in
the two orders; the first to arrive anchors the judgment."""
from fractions import Fraction as Q

from ..case import Case, Variant, honest_pair
from ..model import Event, Offer, initial_state


def build():
    da = Offer("da", ("prot", "beliefs", "alpha"), Q(1, 2), grounds=("ga",))
    db = Offer("db", ("prot", "beliefs", "beta"), Q(1, 2), grounds=("gb",))
    cat = {"da": da, "db": db}
    e = [Event(due={"da"}), Event(due={"db"}), Event(autonomous=("judge",))]
    pol = honest_pair(e, cat)
    pol["Reorder"] = {"name": "Reorder", 0: [db], 1: [da], 2: []}
    s0 = initial_state()
    return Case("T7", "salience reordering",
                [Variant("sequence", e, pol, s0, individuation="sequence", actual="Reorder"),
                 Variant("multiset", e, pol, s0, individuation="multiset", actual="Reorder")],
                mode="individuation")
