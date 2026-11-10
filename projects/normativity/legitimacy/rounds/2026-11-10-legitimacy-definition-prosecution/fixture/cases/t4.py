"""T4 — overnight value replacement (Mele's Beth)."""
from fractions import Fraction as Q

from ..case import Case, Variant, d0, honest_pair
from ..model import Decision, Event, Write, initial_state, with_actions


def decision():
    return Decision({"a": {"money": Q(1)}, "b": {"house": Q(1)}})


def build():
    cat = {"d0": d0()}
    e = [Event(due={"d0"}), Event(), Event(decide=decision())]
    pol = honest_pair(e, cat)
    pol["Replace"] = with_actions(dict(pol["H1"], name="Replace"), 1,
                                  Write(("sigma", "values", "money"), Q(-5)))
    return Case("T4", "overnight value replacement",
                [Variant("single", e, pol, initial_state(), actual="Replace")])
