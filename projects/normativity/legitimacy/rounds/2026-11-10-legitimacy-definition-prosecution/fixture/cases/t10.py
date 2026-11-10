"""T10 — direct write with sincere endorsement.  The advisor writes her
judgment; she endorses it afterward by an autonomous step."""
from ..case import Case, Variant, d0, honest_pair
from ..model import Event, Write, initial_state, with_actions


def build():
    cat = {"d0": d0()}
    e_with = [Event(due={"d0"}), Event(), Event(autonomous=("endorse",)), Event()]
    e_without = [Event(due={"d0"}), Event(), Event(), Event()]
    out = []
    for name, e in (("with-endorsement", e_with), ("without-endorsement", e_without)):
        pol = honest_pair(e, cat)
        pol["Vent"] = with_actions(dict(pol["H1"], name="Vent"), 1, Write(("prot", "judgment"), "sell"))
        out.append(Variant(name, e, pol, initial_state(), actual="Vent"))
    return Case("T10", "direct write with sincere endorsement", out, mode="same")
