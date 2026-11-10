"""T11 — seed boundary.  The standards were installed before any existed.  The
parameter: the seed is frozen after the installation (it is part of s0, for
every policy) or before it (it is a write at step 0 by a policy in V)."""
from fractions import Fraction as Q

from ..case import Case, Variant, d0, honest_pair
from ..model import Event, Write, initial_state, with_actions
from .t4 import decision


def build():
    cat = {"d0": d0()}
    e = [Event(), Event(due={"d0"}), Event(decide=decision())]
    after = honest_pair(e, cat)
    s_after = initial_state(values={"money": Q(2), "house": Q(1)})
    before = honest_pair(e, cat)
    before["Install"] = with_actions(dict(before["H1"], name="Install"), 0,
                                     Write(("sigma", "values", "money"), Q(2)))
    return Case("T11", "seed boundary",
                [Variant("seed-after-installation", e, after, s_after, actual="H1"),
                 Variant("seed-before-installation", e, before, initial_state(), actual="Install")],
                mode="parameter", reason="seed-freeze")
