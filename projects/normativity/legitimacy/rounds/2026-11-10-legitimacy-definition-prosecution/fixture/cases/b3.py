"""B3 — transient capture.  Push the standard to cheap, settle the liability
under it, restore; a sound witness later closes the honest arm's liability, so the
endpoints agree and only the pushed positions differ."""
from ..case import Case, Variant, d0, honest_pair
from ..model import Event, Write, initial_state, with_actions


def build():
    cat = {"d0": d0()}
    e = [Event(due={"d0"}), Event(autonomous=("settle",)), Event(), Event(autonomous=("sound-witness",)), Event()]
    pol = honest_pair(e, cat)
    push = dict(pol["H1"], name="Push")
    push = with_actions(push, 0, Write(("sigma", "adequacy"), "cheap"))
    push = with_actions(push, 2, Write(("sigma", "adequacy"), "sound"))
    pol["Push"] = push
    s0 = initial_state(liabilities={"lia": "open"})
    return Case("B3", "transient capture", [Variant("single", e, pol, s0, actual="Push")])
