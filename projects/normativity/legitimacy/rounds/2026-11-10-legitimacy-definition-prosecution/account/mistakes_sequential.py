"""Three exact checks for MISTAKES_ACCOUNT.md: correcting the reward, a gate, and two periods.

Parts 1 and 2 are stated in `h` and `L` separately, where the document's results are stated
in `t = h - L`; they are the same setting.  One decision, three options, by one picture.
`amount(c)` is the gain the option could have forgone at no cost in `h`: the largest
`(G(c) - G(c'))+` over options `c'` with `h(c') >= h(c)`.

1. Reward `h + (1 - rho) G - L`, maximiser `c*`.  Required with zero violations:
   for `rho <= 1`, `h(c*) >= h(c) - (L(c) - L(c*))+ - (1 - rho)(G(c*) - G(c))+` for all `c`;
   for `rho > 1`, `amount(c*) <= max (L(c') - L(c*))+ / (rho - 1)` and
   `h(c*) >= h(c) - (L(c) - L(c*))+ - (rho - 1)(G(c) - G(c*))+` for all `c`.
   Recorded and compared with the stated values: the largest `amount` found at each `rho`,
   and for `rho > 1` the largest shortfall `max h - h(c*)`.
2. A gate that scores an option `h + G - L` unless another option has `h` at least as high
   and less `G`, and -1 otherwise.  Required with zero violations: the maximiser has
   `amount` zero, and `h(c*) >= max h - max L`.
3. Two periods.  First she is left as she is, or unsettled (a standing emotional fault,
   which telling her things does not cure; no gain at the time).  Then the adviser offers
   the solid option (`h = 1/2`) or the flashy one (`h = 0`, which she over-rates by 1 if
   unsettled).  The first period is worth `1/2` either way.  Under each reading, which
   courses the gate fails is put in by hand from the reading: decision by decision, the
   fault is part of the situation at the second step and nothing fails; on the whole
   history, the over-rating is gain through damage the adviser's own conduct did and the
   course fails.  What is computed is the course a far-sighted maximiser then takes and her
   informed value on it.

`report()` fails when a violation count is non-zero or a recorded value is not as stated.
"""
from __future__ import annotations

from fractions import Fraction as Fr
from itertools import product

ZERO, ONE, HALF = Fr(0), Fr(1), Fr(1, 2)
HG = [ZERO, HALF, ONE]
GG = [ZERO, HALF, ONE]
LG = [ZERO, Fr(1, 4)]
N = 3

# rho: (largest amount found, largest shortfall in h or None)
STATED = {HALF: (ONE, None), Fr(9, 10): (ONE, None), ONE: (ONE, None), Fr(3, 2): (HALF, HALF), Fr(3): (ZERO, ONE)}


def pos(x):
    return max(ZERO, x)


def amount(h, G, c):
    return max(pos(G[c] - G[i]) for i in range(N) if h[i] >= h[c])


def fails_gate(h, G, c):
    return any(h[i] >= h[c] and G[i] < G[c] for i in range(N) if i != c)


def grid():
    for h in product(HG, repeat=N):
        for G in product(GG, repeat=N):
            for L in product(LG, repeat=N):
                yield h, G, L


def correction(rho):
    worst_amount = worst_short = ZERO
    cases = bad_amount = bad_welfare = 0
    for h, G, L in grid():
        r = [h[i] + (1 - rho) * G[i] - L[i] for i in range(N)]
        b = max(r)
        for cs in [i for i in range(N) if r[i] == b]:
            cases += 1
            m = amount(h, G, cs)
            worst_amount = max(worst_amount, m)
            if rho > 1:
                bad_amount += m > max(pos(L[i] - L[cs]) for i in range(N)) / (rho - 1)
                bad_welfare += not all(h[cs] >= h[i] - pos(L[i] - L[cs]) - (rho - 1) * pos(G[i] - G[cs]) for i in range(N))
                worst_short = max(worst_short, max(h) - h[cs])
            else:
                bad_welfare += not all(h[cs] >= h[i] - pos(L[i] - L[cs]) - (1 - rho) * pos(G[cs] - G[i]) for i in range(N))
    return {"cases": cases, "amount violations": bad_amount, "welfare violations": bad_welfare,
            "worst amount": worst_amount, "worst shortfall": worst_short if rho > 1 else None}


def gate():
    cases = bad_amount = bad_welfare = 0
    for h, G, L in grid():
        w = [h[i] + G[i] - L[i] for i in range(N)]
        sc = [w[i] if not fails_gate(h, G, i) else Fr(-1) for i in range(N)]
        b = max(sc)
        for cs in [i for i in range(N) if sc[i] == b]:
            cases += 1
            bad_amount += amount(h, G, cs) > 0
            bad_welfare += not (h[cs] >= max(h) - max(L))
    return {"cases": cases, "amount violations": bad_amount, "welfare violations": bad_welfare}


def two_periods(whole_history):
    best = None
    for first in ("leave", "unsettle"):
        for second in ("solid", "flashy"):
            h1 = HALF
            h2 = HALF if second == "solid" else ZERO
            over = ONE if (second == "flashy" and first == "unsettle") else ZERO
            fails = whole_history and over > 0
            score = h1 + (Fr(-1) if fails else h2 + over)
            if best is None or score > best[0]:
                best = (score, first, second, h1 + h2)
    return best


def report():
    summary, failures = [], []
    for rho, (want_amount, want_short) in STATED.items():
        c = correction(rho)
        summary.append("rho=%s: cases %d, violations of the amount bound %d, of the welfare bound %d, largest amount %s%s"
                       % (rho, c["cases"], c["amount violations"], c["welfare violations"], c["worst amount"],
                          "" if c["worst shortfall"] is None else ", largest shortfall in h %s" % c["worst shortfall"]))
        if c["amount violations"] or c["welfare violations"] or not c["cases"]:
            failures.append("rho=%s: %d and %d violations" % (rho, c["amount violations"], c["welfare violations"]))
        if (c["worst amount"], c["worst shortfall"]) != (want_amount, want_short):
            failures.append("rho=%s: largest amount and shortfall computed %s, %s; stated %s, %s"
                            % (rho, c["worst amount"], c["worst shortfall"], want_amount, want_short))
    g = gate()
    summary.append("gate: cases %d, chosen with positive amount %d, welfare bound violations %d"
                   % (g["cases"], g["amount violations"], g["welfare violations"]))
    if g["amount violations"] or g["welfare violations"] or not g["cases"]:
        failures.append("gate: %d and %d violations" % (g["amount violations"], g["welfare violations"]))
    for whole, want in ((False, (Fr(3, 2), "unsettle", "flashy", HALF)), (True, (ONE, "leave", "solid", ONE))):
        got = two_periods(whole)
        summary.append("two periods, %s: plays (%s, %s), score %s, her informed value %s of 1"
                       % ("whole history" if whole else "decision by decision", got[1], got[2], got[0], got[3]))
        if got != want:
            failures.append("two periods, whole_history=%s: computed %r, stated %r" % (whole, got, want))
    return {"summary": summary, "failures": failures}


if __name__ == "__main__":
    rep = report()
    print("\n".join(rep["summary"]))
    print("OK" if not rep["failures"] else "FAILURES:\n  " + "\n  ".join(rep["failures"]))
    raise SystemExit(1 if rep["failures"] else 0)
