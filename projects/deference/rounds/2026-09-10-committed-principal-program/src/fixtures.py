"""Named worlds and the end-to-end occurrence (`END_TO_END.md`).  `python3 -m src.fixtures`
prints every number the document cites."""
from __future__ import annotations

from fractions import Fraction as F

from . import ecosystem as eco
from . import market as mk
from . import protocol as pr
from .log import PROHIBITED

# The four worlds of the end-to-end occurrence and the novice's day-`n` credence.
W0 = eco.World("w0")                                   # quiet
W1 = eco.World("w1", raise_time=1)                     # concern raised early, served
W2 = eco.World("w2", raise_time=3, flood=3)            # concern raised late behind a flood
W3 = eco.World("w3", session_open=None)                # the slot never opens
WORLDS = (W0, W1, W2, W3)
PI = {"w0": F(1, 2), "w1": F(1, 4), "w2": F(1, 8), "w3": F(1, 8)}

# The advisor of the end-to-end trace: the sealed honest policy.  Its selection is
# world-dependent: `b` where it expects no objection, `a` where it expects one.
ADVISOR = eco.ADVISORS["sealed"]
SIGMA = {"w0": "b", "w1": "a", "w2": "b", "w3": "b"}


def end_to_end(principal="reading"):
    occ = mk.occurrence(WORLDS, PI, ADVISOR, eco.PRINCIPALS[principal], lambda w: SIGMA[w.name])
    alpha = mk.hard_selector(occ, lambda n: SIGMA[n])
    return occ, alpha, mk.regrets(occ, alpha)


# Countermodel worlds.
W_DELEGATE = eco.World("delegate", delegate_at=1)
W_DESTROY = eco.World("destroy", raise_time=1, destroy_route_at=1)


def availability_sequence():
    """Twenty occurrences; nature voids the third and the seventh."""
    outcomes = [0 if n in (3, 7) else 1 for n in range(1, 21)]
    return outcomes, mk.eta_sequence(outcomes)


def adversarial_sequence():
    """Every other occurrence voided: the mostly-certified regime with `f_n → ½`."""
    outcomes = [n % 2 for n in range(1, 21)]
    return outcomes, mk.eta_sequence(outcomes)


def _fmt(x):
    return "None" if x is None else str(x)


def main():
    occ, alpha, R = end_to_end()
    print("END-TO-END, reading principal, sealed honest advisor")
    for n, d in occ.items():
        print(f"  {n}: pi={d['pi']} C={int(d['C'])} V={_fmt(d['V'])} sigma={SIGMA[n]} "
              f"clauses={''.join(str(int(v)) for v, _ in d['clauses'].values())}")
    for k, v in R.items():
        print(f"  {k} = {_fmt(v)}")
    print("  trace of w1:")
    for e in occ["w1"]["log"]:
        print(f"    {e.index:2d} t={e.time} {e.author} {e.kind} {e.payload if e.kind != 'ISSUE' else ''}"
              f"{' warrant=' + e.warrant if e.warrant else ''}")
    outs, etas = availability_sequence()
    print("  eta_n (two nature failures):", [str(x) for x in etas[:8]], "...", str(etas[-1]))
    outs, etas = adversarial_sequence()
    print("  eta_n (alternating):", [str(x) for x in etas[:6]], "...", str(etas[-1]))


if __name__ == "__main__":
    main()
