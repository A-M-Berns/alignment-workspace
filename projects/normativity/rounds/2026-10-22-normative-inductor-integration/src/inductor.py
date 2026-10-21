"""The grounded survivor rule, the run's fixture, and the adapter's constants — exact rationals.

Mirrors `WarrantEntitlement.lean` (`Grounds.survivors` as the least fixed point of
`activeStep`), `WarrantInductor.lean` (the canonical bundle, `compileAt`, the problem's
`κ`, `massCap`, the gate) and `WarrantInductorWitness.lean` (the fixture).  Coordinates are
`X, XA, XAY, Y, Z` = `0..4`; a settlement is a tuple of `None | True | False`; forms are
`('premise', X, c)`, `('applicability', X, XA, c)`, `('strength', XA, XAY, c)`.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F

KEPT, REBUTTED, VACUOUS, RETIRED = "kept", "rebutted", "vacuous", "retired"
X, XA, XAY, Y, Z = range(5)


# ---------------------------------------------------------------------------
# Forms, rows, settlement

def row_of(form) -> tuple[list[F], F]:
    """`a · x ≤ b` on five coordinates, as `Form.row`."""
    a = [F(0)] * 5
    if form[0] == "premise":
        _, i, c = form
        a[i] = F(-1)
        return a, -F(c)
    if form[0] == "applicability":
        _, i, j, c = form
        a[i] += F(c)
        a[j] += F(-1)
        return a, F(0)
    _, i, j, c = form
    a[i] += F(c)
    a[j] += F(-1)
    return a, F(0)


def pins_false(settlement, i: int) -> bool:
    return settlement[i] is False


def settle_outcome(settlement, form) -> str:
    """`settleOutcome`: vacuity before rebuttal."""
    if form[0] == "premise":
        return RETIRED if pins_false(settlement, form[1]) else KEPT
    _, ante, cons, _ = form
    if pins_false(settlement, ante):
        return VACUOUS
    if pins_false(settlement, cons):
        return REBUTTED
    return KEPT


def specialize(settlement, row):
    """`specialize`: settled coordinates substituted, zero coefficient left behind."""
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


# ---------------------------------------------------------------------------
# Occurrences and the grounded survivor rule

@dataclass(frozen=True)
class Occurrence:
    id: int
    form: tuple
    cites: int | None
    source: str
    defeaters: frozenset = frozenset()


def undercut(defeated: set[int], o: Occurrence) -> bool:
    return o.id in defeated or any(j in defeated for j in o.defeaters)


def live_given(defeated, settlement, S: set[int], o: Occurrence) -> bool:
    return (not undercut(defeated, o)
            and settle_outcome(settlement, o.form) == KEPT
            and (o.cites is None or o.cites in S))


def active_step(G, defeated, settlement, S: set[int]) -> set[int]:
    return {o.id for o in G if live_given(defeated, settlement, S, o)}


def active_ids(G, defeated, settlement) -> set[int]:
    """`Grounds.activeIds`: the step iterated `len(G)` times from the empty set."""
    S: set[int] = set()
    for _ in range(len(G)):
        S = active_step(G, defeated, settlement, S)
    return S


def survivors(G, defeated, settlement) -> list[Occurrence]:
    """`Grounds.survivors`: live given the active identities."""
    S = active_ids(G, defeated, settlement)
    return [o for o in G if live_given(defeated, settlement, S, o)]


def one_step_survivors(G, defeated, settlement) -> list[Occurrence]:
    """The rebuttal round's rule: retirement one step along `cites`, no undercut propagation."""
    retired = {o.id for o in G if settle_outcome(settlement, o.form) == RETIRED}
    return [o for o in G if o.id not in defeated
            and settle_outcome(settlement, o.form) == KEPT
            and not (o.cites is not None and o.cites in retired)]


# ---------------------------------------------------------------------------
# The canonical bundle and its region

def bundle(G, structural, defeated, settlement):
    """`NormState.bundle`: survivors' specialized rows, live structural rows, pins; cited."""
    rows = [(("sub", o.id), specialize(settlement, row_of(o.form)))
            for o in survivors(G, defeated, settlement)]
    rows += [(("str", sid), specialize(settlement, row)) for sid, row in structural]
    rows += pin_rows(settlement)
    return rows


def in_region(B, x) -> bool:
    """`Bundle.Region`: the cube and every cited row."""
    return all(F(0) <= v <= 1 for v in x) and all(
        sum(ai * xi for ai, xi in zip(a, x)) <= b for _, (a, b) in B)


def compile_at(B, witness):
    """`compileAt`: the bundle when the witness checks, nothing otherwise."""
    return B if in_region(B, witness) else []


def excess(row, p) -> F:
    a, b = row
    return sum(ai * pi for ai, pi in zip(a, p)) - b


# ---------------------------------------------------------------------------
# Certificates

def functional_of(mults, rows):
    """`Σ mult_i · a_i`, the functional a certificate certifies."""
    return [sum(m * a[j] for m, (a, _) in zip(mults, rows)) for j in range(5)]


def cert_value(mults, rows) -> F:
    return sum(m * b for m, (_, b) in zip(mults, rows))


def cert_mass(mults) -> F:
    return sum(mults)


def transport_bound(mults, rows, delta) -> F:
    """`FunctionalCert.le_of_excess`: `value + mass · δ`."""
    return cert_value(mults, rows) + cert_mass(mults) * delta


# ---------------------------------------------------------------------------
# The soft gate

def ramp(x: F) -> F:
    return max(F(0), min(F(1), x))


def soft_gate(scores, pref, tau, delta):
    w = [ramp((s - tau) / delta) * p for s, p in zip(scores, pref)]
    total = sum(w)
    return [wi / total for wi in w] if total > 0 else None


def kappa(pref, adequate, W, delta) -> F:
    """`Problem.κ = (Σ_{q∉A} pref q) / W / δ`."""
    return sum(p for q, p in enumerate(pref) if q not in adequate) / W / delta


# ---------------------------------------------------------------------------
# The fixture of `WarrantInductorWitness.lean`

C = dict(P=F(4, 5), A=F(3, 4), S=F(2, 3), Z=F(3, 4))
N1, N0, NE = 3, 5, 8
RHO = F(4)
TOL = F(1, 400)

occP = Occurrence(1, ("premise", X, C["P"]), None, "party 1")
occA = Occurrence(2, ("applicability", X, XA, C["A"]), 1, "party 1")
occS = Occurrence(3, ("strength", XA, XAY, C["S"]), 2, "party 1", frozenset({2}))
occZ = Occurrence(4, ("premise", Z, C["Z"]), None, "party 2")
GROUNDS = [occP, occA, occS, occZ]

COHERENCE = [(10, ([F(-1), F(1), F(0), F(0), F(0)], F(0))),   # XA ≤ X
             (11, ([F(0), F(-1), F(1), F(0), F(0)], F(0))),   # XAY ≤ XA
             (12, ([F(0), F(0), F(1), F(-1), F(0)], F(0)))]   # XAY ≤ Y


def settlement_at(n: int):
    return (True if n >= N1 else None, None,
            False if n >= NE else None, False if n >= NE else None, None)


def defeated_at(n: int) -> set[int]:
    return {2} if n >= N0 else set()


def witness_at(n: int):
    return [F(1)] * 5 if n < NE else [F(1), F(1), F(0), F(0), F(1)]


def state_bundle(n: int):
    return bundle(GROUNDS, COHERENCE, defeated_at(n), settlement_at(n))


def enforced_bundle(n: int):
    return compile_at(state_bundle(n), witness_at(n))


def seed_gap(row, world) -> F:
    """`seedGap`: `b − a · payout`."""
    a, b = row
    return b - sum(ai * wi for ai, wi in zip(a, world))


ALL_TRUE = [F(1), F(1), F(1), F(1), F(1)]          # X, XA, XAY, Y, Z all true
W_AY = [F(1), F(1), F(0), F(0), F(1)]              # X, A, Z true, Y false


def worlds_pinned_by(settlement):
    """All 0/1 worlds (over the atoms X, A, Y, Z) whose payouts the settlement pins."""
    out = []
    for bits in range(16):
        x, a, y, z = (bits >> 3) & 1, (bits >> 2) & 1, (bits >> 1) & 1, bits & 1
        world = [F(x), F(x * a), F(x * a * y), F(y), F(z)]
        if all(s is None or world[i] == (F(1) if s else F(0)) for i, s in enumerate(settlement)):
            out.append(world)
    return out


def dominated(B, slack, worlds, rho=RHO) -> bool:
    """`−gap_w ≤ ρ · gap_slack` on every row for every live world `w`."""
    return all(-seed_gap(row, w) <= rho * seed_gap(row, slack) for _, row in B for w in worlds)


def bankroll_reopened(rho=RHO, cap=F(3)) -> F:
    return cap * rho * (2 + rho)


# The two problems
P1 = dict(offset=[F(0), F(0)], ell=[[F(0), F(0), F(1), F(0), F(0)], [F(0), F(1), F(-1), F(0), F(0)]],
          adequate={0}, pref=[F(1), F(1)], tau=F(1, 3), delta=F(1, 12), W=F(1))
P2 = dict(offset=[F(0), F(1)], ell=[[F(0), F(0), F(0), F(0), F(1)], [F(0), F(0), F(0), F(0), F(-1)]],
          adequate={0}, pref=[F(1), F(1)], tau=F(1, 4), delta=F(1, 4), W=F(1))


def score(P, q, p) -> F:
    return P["offset"][q] + sum(l * pi for l, pi in zip(P["ell"][q], p))


def cube_upper(i):
    e = [F(0)] * 5
    e[i] = F(1)
    return e, F(1)


def cube_lower(i):
    e = [F(0)] * 5
    e[i] = F(-1)
    return e, F(0)


def row_in_bundle(B, cite, row) -> bool:
    return (cite, row) in B


# the certificates of date 4 and date 9, as (mults, rows, cites)
def certificates():
    s4, s9 = settlement_at(4), settlement_at(9)
    rowS4 = specialize(s4, row_of(occS.form))
    rowA4 = specialize(s4, row_of(occA.form))
    rowZ9 = specialize(s9, row_of(occZ.form))
    upS = ([F(1), F(1, 3)], [rowS4, cube_upper(XA)], [("sub", 3), None])
    loS = ([F(1), F(2, 3)], [rowS4, rowA4], [("sub", 3), ("sub", 2)])
    certZ = ([F(1)], [rowZ9], [("sub", 4)])
    return dict(upS=upS, loS=loS, certZ=certZ)
