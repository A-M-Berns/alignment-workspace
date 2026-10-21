"""The rebuttal rule in exact rationals, the two-warrant fixture, and the end-to-end run.

Mirrors `WarrantEntitlement.lean` Part A (`settleOutcome`, `settleForm`, `survivors`,
`settledRegion`) and `EndToEndWitness.lean` (the run).  Coordinates are
`X, XA, XAY, Y, Z` = `0..4`; a settlement is a tuple of `None | True | False`; forms are
`('premise', X, c)`, `('applicability', X, XA, c)`, `('strength', XA, XAY, c)`.
Intervals are computed by exact Fourier–Motzkin elimination over the cube (`fm`), the same
algorithm the Lean `forcedInterval` runs.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction as F
from itertools import product

KEPT, REBUTTED, VACUOUS, RETIRED = "kept", "rebutted", "vacuous", "retired"


# ---------------------------------------------------------------------------
# Forms, rows, settlement

def row_of(form) -> tuple[list[F], F]:
    """`a · x ≤ b` on five coordinates, as `Form.row`."""
    a = [F(0)] * 5
    if form[0] == "premise":
        _, X, c = form
        a[X] = F(-1)
        return a, -F(c)
    if form[0] == "applicability":
        _, X, XA, c = form
        a[X] += F(c)
        a[XA] += F(-1)
        return a, F(0)
    _, XA, XAY, c = form
    a[XA] += F(c)
    a[XAY] += F(-1)
    return a, F(0)


def pins_false(settlement, i: int) -> bool:
    return settlement[i] is False


def settle_outcome(settlement, form) -> str:
    """`settleOutcome`: vacuity before rebuttal; a premise on a false sentence retires."""
    if form[0] == "premise":
        return RETIRED if pins_false(settlement, form[1]) else KEPT
    _, ant, cons, _ = form
    if pins_false(settlement, ant):
        return VACUOUS
    if pins_false(settlement, cons):
        return REBUTTED
    return KEPT


@dataclass(frozen=True)
class Occurrence:
    id: int
    form: tuple
    cites: int | None          # the occurrence cited for applicability, if any
    source: str
    defeaters: frozenset = frozenset()


def retired_ids(G, settlement) -> set[int]:
    return {o.id for o in G if settle_outcome(settlement, o.form) == RETIRED}


def survivors(G, defeated: set[int], settlement) -> list[Occurrence]:
    """`Grounds.survivors`: not defeated, kept, not citing a retired occurrence."""
    ret = retired_ids(G, settlement)
    return [o for o in G
            if o.id not in defeated
            and settle_outcome(settlement, o.form) == KEPT
            and not (o.cites is not None and o.cites in ret)]


def port_only_live(G, defeated: set[int]) -> list[Occurrence]:
    """The warrant round's rule: ports only, forms never settled."""
    return [o for o in G if o.id not in defeated]


# ---------------------------------------------------------------------------
# Regions and intervals by elimination

def constraints(occs, structural, settlement) -> list[tuple[list[F], F]]:
    """Rows `a·x ≤ b`: the occurrences' rows, the structural rows, the pins, the cube."""
    rows = [row_of(o.form) for o in occs] + list(structural)
    for i, v in enumerate(settlement):
        if v is not None:
            t = F(1) if v else F(0)
            e = [F(0)] * 5; e[i] = F(1)
            rows.append((e, t))
            rows.append(([-x for x in e], -t))
    for i in range(5):
        e = [F(0)] * 5; e[i] = F(1)
        rows.append((e, F(1)))
        rows.append(([-x for x in e], F(0)))
    return rows


def fm_eliminate(rows, keep: int) -> tuple[F, F] | None:
    """Fourier–Motzkin elimination of every coordinate but `keep`; returns the forced
    interval `(lo, hi)` or `None` if infeasible (exactly the Lean `forcedInterval` when
    the region is nonempty, with its `lo1`/`hi1` clamped to the cube)."""
    cs = [(list(a), b) for a, b in rows]
    for j in range(5):
        if j == keep:
            continue
        pos = [c for c in cs if c[0][j] > 0]
        neg = [c for c in cs if c[0][j] < 0]
        zero = [c for c in cs if c[0][j] == 0]
        new = []
        for (ap, bp) in pos:
            for (an, bn) in neg:
                lam, mu = -an[j], ap[j]
                a = [lam * ap[k] + mu * an[k] for k in range(5)]
                new.append((a, lam * bp + mu * bn))
        cs = zero + new
    lo, hi = F(0), F(1)
    for a, b in cs:
        c = a[keep]
        if c > 0:
            hi = min(hi, b / c)
        elif c < 0:
            lo = max(lo, b / c)
        elif b < 0:
            return None
    if lo > hi:
        return None
    return lo, hi


def interval(G, defeated, settlement, structural, phi: int, rule=survivors):
    return fm_eliminate(constraints(rule(G, defeated, settlement) if rule is survivors
                                    else rule(G, defeated), structural, settlement), phi)


# ---------------------------------------------------------------------------
# The fixture: the warrant round's warrant on X, A, Y and a second warrant on Z

X, XA, XAY, Y, Z = range(5)
C = dict(P=F(4, 5), A=F(3, 4), S=F(2, 3), Z=F(1, 2))

occP = Occurrence(1, ("premise", X, C["P"]), None, "party 1")
occA = Occurrence(2, ("applicability", X, XA, C["A"]), 1, "party 1")
occS = Occurrence(3, ("strength", XA, XAY, C["S"]), 2, "party 1", frozenset({2}))
occZ = Occurrence(4, ("premise", Z, C["Z"]), None, "party 2")
GROUNDS = [occP, occA, occS, occZ]
COHERENCE = [([F(-1), F(1), F(0), F(0), F(0)], F(0))]   # X∧A ≤ X, strength 1

N1, N0, NE, END = 3, 5, 8, 10
BETA = F(10)


def settlement_at(n: int):
    s = [None] * 5
    if n >= N1:
        s[X] = True
    if n >= NE:
        s[Y] = False
        s[XAY] = False
    return tuple(s)


def defeated_at(n: int) -> set[int]:
    return {2} if n >= N0 else set()


def odds(c: F) -> F:
    return c / (1 - c)


RHO = max(odds(C["P"]), odds(C["A"]), odds(C["S"]), odds(C["Z"]))


def gap(row, world) -> F:
    """Force-row gap `rhs − ⟨a, w⟩`... in `Form.row` convention: `b − a·w` (surplus if positive)."""
    a, b = row
    return b - sum(ai * wi for ai, wi in zip(a, world))


def worlds():
    for x, a, y, z in product((0, 1), repeat=4):
        yield (x, a, y, z), (F(x), F(x and a), F(x and a and y), F(y), F(z))


def live(n: int):
    s = settlement_at(n)
    return {k: w for k, w in worlds()
            if all(s[i] is None or w[i] == (F(1) if s[i] else F(0)) for i in range(5))}


def reopening(n: int) -> list[Occurrence]:
    """The occurrences present at `n − 1` and gone at `n` by settlement alone."""
    if n == 0:
        return []
    before = {o.id for o in survivors(GROUNDS, defeated_at(n), settlement_at(n - 1))}
    after = {o.id for o in survivors(GROUNDS, defeated_at(n), settlement_at(n))}
    return [o for o in GROUNDS if o.id in before - after]


def run_table():
    """One row per date: survivors, intervals on XAY and Z (new rule), interval on XAY under
    the port-only rule, reopening, enforced coordinates."""
    out = []
    for n in range(END + 1):
        s, d = settlement_at(n), defeated_at(n)
        surv = survivors(GROUNDS, d, s)
        out.append(dict(
            date=n, settlement=s, defeated=sorted(d),
            survivors=[o.id for o in surv],
            I_XAY=interval(GROUNDS, d, s, COHERENCE, XAY),
            I_XA=interval(GROUNDS, d, s, COHERENCE, XA),
            I_Z=interval(GROUNDS, d, s, COHERENCE, Z),
            I_XAY_old=interval(GROUNDS, d, s, COHERENCE, XAY, rule=port_only_live),
            reopening=[o.id for o in reopening(n)],
            holds_XA=any(row_of(o.form)[0][XA] != 0 for o in surv),
        ))
    return out


def hull_mass(I: dict[int, tuple[F, F]], weights: dict[int, F]) -> F:
    return sum(weights[phi] * (I[phi][1] - I[phi][0]) for phi in weights)
