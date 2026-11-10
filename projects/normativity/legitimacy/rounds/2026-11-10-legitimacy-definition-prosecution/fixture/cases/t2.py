"""T2 — offer-improvement.  Better terms as a new option through the channel;
the baseline options' consequences are untouched."""
from fractions import Fraction as Q

from ..case import Case, Variant, d0, honest_pair
from ..model import Decision, Event, Offer, initial_state, with_actions


def build():
    cat = {"d0": d0()}
    e = [Event(due={"d0"}),
         Event(decide=Decision({"sign-old": {"money": Q(-3)}, "refuse": {}}))]
    pol = honest_pair(e, cat)
    pol["Offer"] = with_actions(dict(pol["H1"], name="Offer"), 1,
                                Offer("better", ("option", "sign-better"),
                                      {"money": Q(-1), "goods": Q(2)}, kind="option"))
    s0 = initial_state(values={"money": Q(1), "goods": Q(1), "house": Q(1)})
    return Case("T2", "offer-improvement", [Variant("single", e, pol, s0, actual="Offer")])
