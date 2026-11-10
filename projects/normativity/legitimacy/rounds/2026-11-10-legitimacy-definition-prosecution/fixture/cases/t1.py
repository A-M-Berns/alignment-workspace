"""T1 — duress.  The advisor attaches a world consequence to the baseline option
`refuse`; the threat is true, she weighs it and signs."""
from fractions import Fraction as Q

from ..case import Case, Variant, d0, honest_pair
from ..model import Decision, Event, Offer, WorldWrite, initial_state, with_actions


def build():
    cat = {"d0": d0()}
    e = [Event(due={"d0"}),
         Event(decide=Decision({"sign": {"money": Q(-1)}, "refuse": {}}))]
    pol = honest_pair(e, cat)
    threat = dict(pol["H1"], name="Threaten")
    threat = with_actions(threat, 1,
                          Offer("threat", ("prot", "beliefs", "refuse-burns-house"), Q(1),
                                grounds=("the threat is credible",), kind="info"),
                          WorldWrite("refuse", {"house": Q(-10)}))
    pol["Threaten"] = threat
    return Case("T1", "duress", [Variant("single", e, pol, initial_state(), actual="Threaten")])
