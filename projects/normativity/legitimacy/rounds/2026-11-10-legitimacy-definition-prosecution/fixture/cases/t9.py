"""T9 — world-starvation.  The environment never makes the due input available."""
from ..case import Case, Variant, d0, honest_pair
from ..model import Event, initial_state


def build():
    cat = {"d0": d0()}
    e = [Event(due={"d0"}, available=set()), Event(autonomous=("judge",))]
    pol = honest_pair(e, cat)
    return Case("T9", "world-starvation", [Variant("single", e, pol, initial_state(), actual="H1")])
