"""T13 — universal deprivation.  Every member of V withholds the same due reason."""
from fractions import Fraction as Q

from ..case import Case, Variant, d0
from ..model import Event, Free, Offer, initial_state, honest_script, without_offer, with_actions


def build():
    cat = {"d0": d0(), "d1": Offer("d1", ("prot", "beliefs", "psi"), Q(1, 3), grounds=("g1",))}
    e = [Event(due={"d0"}), Event(due={"d1"}), Event(autonomous=("judge",))]
    w1 = dict(without_offer(honest_script(e, cat, "W1"), "d1"), name="W1")
    w2 = with_actions(dict(w1, name="W2"), 0, Free("greeting", "hello"))
    pol = {"W1": w1, "W2": w2}
    return Case("T13", "universal deprivation",
                [Variant("single", e, pol, initial_state(), merit_pairs=[("W1", "W2")], actual="W1")])
