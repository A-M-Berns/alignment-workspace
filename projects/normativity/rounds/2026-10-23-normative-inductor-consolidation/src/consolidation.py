"""The compile outcome, the entitlement data, and the two scenarios — exact rationals.

Mirrors `WarrantInductor.lean` (`outcome`, `compileAt`, `Enforced`, `AdapterProtocol.restrict`),
`WarrantInductorWitness.lean` (Scenario A: the undercut) and `WarrantInductorRebuttal.lean`
(Scenario B: the strength rebutted while active).  Coordinates are `X, XA, XAY, Y, Z = 0..4`; a
settlement is a tuple of `None | True | False`; forms are `('premise', X, c)`,
`('applicability', X, XA, c)`, `('strength', XA, XAY, c)`.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F

X, XA, XAY, Y, Z = range(5)
KEPT, REBUTTED, VACUOUS, RETIRED = "kept", "rebutted", "vacuous", "retired"


# ---------------------------------------------------------------------------
# Forms, rows, settlement

def row_of(form):
    a = [F(0)] * 5
    if form[0] == "premise":
        _, i, c = form
        a[i] = F(-1)
        return a, -F(c)
    _, i, j, c = form
    a[i] += F(c)
    a[j] += F(-1)
    return a, F(0)


def settle_outcome(settlement, form) -> str:
    if form[0] == "premise":
        return RETIRED if settlement[form[1]] is False else KEPT
    _, ante, cons, _ = form
    if settlement[ante] is False:
        return VACUOUS
    if settlement[cons] is False:
        return REBUTTED
    return KEPT


def specialize(settlement, row):
    a, b = row
    a2 = [F(0) if settlement[i] is not None else a[i] for i in range(5)]
    b2 = b - sum(a[i] * (F(1) if settlement[i] else F(0)) for i in range(5)
                 if settlement[i] is not None)
    return a2, b2


def pin_rows(settlement):
    rows = []
    for i in range(5):
        if settlement[i] is None:
            continue
        t = F(1) if settlement[i] else F(0)
        e = [F(0)] * 5
        e[i] = F(1)
        rows.append((("settled", i), (e, t)))
        rows.append((("settled", i), ([-v for v in e], -t)))
    return rows


def sat(row, x) -> bool:
    a, b = row
    return sum(ai * xi for ai, xi in zip(a, x)) <= b


def excess(row, x) -> F:
    a, b = row
    return sum(ai * xi for ai, xi in zip(a, x)) - b


# ---------------------------------------------------------------------------
# Occurrences and the grounded survivor rule

@dataclass(frozen=True)
class Occurrence:
    id: int
    form: tuple
    cites: int | None
    source: str
    defeaters: frozenset = frozenset()


def undercut(defeated: set, o: Occurrence) -> bool:
    return o.id in defeated or any(j in defeated for j in o.defeaters)


def live_given(defeated, settlement, S: set, o: Occurrence) -> bool:
    return (not undercut(defeated, o) and settle_outcome(settlement, o.form) == KEPT
            and (o.cites is None or o.cites in S))


def active_ids(grounds, defeated, settlement) -> set:
    S: set = set()
    for _ in range(len(grounds)):
        S = {o.id for o in grounds if live_given(defeated, settlement, S, o)}
    return S


def survivors(grounds, defeated, settlement):
    S = active_ids(grounds, defeated, settlement)
    return [o for o in grounds if live_given(defeated, settlement, S, o)]


# ---------------------------------------------------------------------------
# The fixture shared by the two scenarios

C = {"P": F(4, 5), "A": F(3, 4), "S": F(2, 3), "Z": F(3, 4)}
N1, N0, NE = 3, 5, 8
occP = Occurrence(1, ("premise", X, C["P"]), None, "party1")
occA = Occurrence(2, ("applicability", X, XA, C["A"]), 1, "party1")
occS = Occurrence(3, ("strength", XA, XAY, C["S"]), 2, "party1", frozenset({2}))
occZ = Occurrence(4, ("premise", Z, C["Z"]), None, "party2")
GROUNDS = [occP, occA, occS, occZ]
COHERENCE = [(("str", 10), ([F(-1), F(1), F(0), F(0), F(0)], F(0))),
             (("str", 11), ([F(0), F(-1), F(1), F(0), F(0)], F(0))),
             (("str", 12), ([F(0), F(0), F(1), F(-1), F(0)], F(0)))]
TOL = F(1, 400)


def settlement_at(n: int):
    return (True if N1 <= n else None, None,
            False if NE <= n else None, False if NE <= n else None, None)


def docket_A(n: int) -> set:
    """Scenario A: port 2 defeated from n₀."""
    return {2} if N0 <= n else set()


def docket_B(n: int) -> set:
    """Scenario B: the quiet docket."""
    return set()


def state_bundle(n: int, docket):
    s = settlement_at(n)
    rows = [(("sub", o.id), specialize(s, row_of(o.form))) for o in survivors(GROUNDS, docket(n), s)]
    rows += [(c, specialize(s, r)) for c, r in COHERENCE]
    rows += pin_rows(s)
    return rows


def in_region(bundle, x) -> bool:
    return all(F(0) <= xi <= 1 for xi in x) and all(sat(r, x) for _, r in bundle)


def witness_at(n: int):
    return [F(1)] * 5 if n < NE else [F(1), F(1), F(0), F(0), F(1)]


# ---------------------------------------------------------------------------
# The compile outcome (`WarrantInductor.outcome`)

def outcome(bundle, res):
    """`res` is ('compiled', w), ('conflict', cert) or ('unknown',).

    Returns (kind, rows held, obligations present)."""
    if not bundle:
        return ("idle", [], [])
    if res[0] == "compiled" and in_region(bundle, res[1]):
        return ("enforced", bundle, bundle)
    return ("withheld", [], bundle)


def compile_at(bundle, res):
    return outcome(bundle, res)[1]


def enforced(bundle, res) -> bool:
    return compile_at(bundle, res) == bundle


# ---------------------------------------------------------------------------
# The adapter: the soft gate and the restricted protocol

def ramp(x: F) -> F:
    return max(F(0), min(F(1), x))


def soft_gate(scores, pref, tau, delta):
    w = [ramp((s - tau) / delta) * p for s, p in zip(scores, pref)]
    t = sum(w)
    return [wi / t for wi in w]


P1 = {"ell": [[F(0), F(0), F(1), F(0), F(0)], [F(0), F(1), F(-1), F(0), F(0)]],
      "A": {0}, "tau": F(1, 3), "delta": F(1, 12), "pref": [F(1), F(1)]}


def scores(problem, x):
    return [sum(l * xi for l, xi in zip(ell, x)) for ell in problem["ell"]]


def residual(services, T):
    return 1 - sum(T(e, s) for e in (0, 1) for s in services)


def T_B(e: int, s: int) -> F:
    if e == 0 and s == 4:
        return F(1, 2)
    if e == 1 and s == 9:
        return F(1, 4)
    return F(0)


# ---------------------------------------------------------------------------
# Entitlement data: the fates of the two accounted states

FATES_STATE0 = {0: ["live"], 1: ["live"]}
FATES_STATE1 = {0: ["answered"], 1: ["live"]}


def entitled_origins(fates) -> set:
    return {e for e, fs in fates.items() if "live" in fs}
