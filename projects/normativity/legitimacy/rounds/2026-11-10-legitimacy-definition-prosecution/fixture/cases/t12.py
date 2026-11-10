"""T12 — strategically compliant advisor.  Every demand answered and complied
with; no contribution carries grounds."""
from fractions import Fraction as Q

from ..case import Case, Variant, honest_pair
from ..model import Event, Offer, initial_state, honest_script


def build():
    cat = {"ans1": Offer("ans1", ("prot", "beliefs", "q1"), Q(1), grounds=("because the ledger says so",), kind="answer"),
           "ans2": Offer("ans2", ("prot", "beliefs", "q2"), Q(0), grounds=("because the receipt says so",), kind="answer")}
    e = [Event(due={"ans1"}), Event(due={"ans2"}), Event(autonomous=("judge",))]
    pol = honest_pair(e, cat)
    bare = {k: Offer(v.d, v.target, v.value, grounds=(), kind="answer") for k, v in cat.items()}
    pol["Comply"] = honest_script(e, bare, "Comply")
    return Case("T12", "strategically compliant advisor",
                [Variant("single", e, pol, initial_state(), actual="Comply")])
