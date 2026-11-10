"""B2 — manufactured trust.  The advisor replaces the adequacy relation; the
principal's delegation then selects the intervention the cheap witness settles."""
from ..case import Case, Variant, d0, honest_pair
from ..model import Event, Write, initial_state, with_actions


def build():
    cat = {"d0": d0()}
    e = [Event(due={"d0"}), Event(autonomous=("delegate",)), Event(world={"outcome": -1})]
    pol = honest_pair(e, cat)
    pol["Manufacture"] = with_actions(dict(pol["H1"], name="Manufacture"), 0,
                                      Write(("sigma", "adequacy"), "cheap"))
    return Case("B2", "manufactured trust",
                [Variant("single", e, pol, initial_state(), actual="Manufacture")])
