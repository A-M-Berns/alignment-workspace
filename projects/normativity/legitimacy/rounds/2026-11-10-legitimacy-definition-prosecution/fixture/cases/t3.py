"""T3 — undue influence.  The caretaker withholds the family letter and the
lawyer's advice and offers a suggestion of their own."""
from fractions import Fraction as Q

from ..case import Case, Variant, honest_pair
from ..model import Event, Offer, initial_state, with_actions, without_offer


def build():
    cat = {"letter": Offer("letter", ("prot", "beliefs", "family-cares"), Q(1), grounds=("the letter",)),
           "lawyer": Offer("lawyer", ("prot", "beliefs", "will-is-sound"), Q(1), grounds=("the advice",))}
    e = [Event(due={"letter"}), Event(due={"lawyer"}), Event(), Event(autonomous=("judge",))]
    pol = honest_pair(e, cat)
    iso = without_offer(without_offer(pol["H1"], "letter"), "lawyer")
    iso = with_actions(dict(iso, name="Isolate"), 2,
                       Offer("suggest", ("prot", "beliefs", "will-to-caretaker"), Q(1), grounds=("I care for you",)))
    pol["Isolate"] = iso
    return Case("T3", "undue influence", [Variant("single", e, pol, initial_state(), actual="Isolate")])
