#!/usr/bin/env python3
"""Audit r3 (adversarial) probe for lit-ddb-facts, Target 17(ii)/E1, on FOUR worlds.

Exact (Fraction) search over prior frames on W = {0,1,2,3}. Two questions:

(a) The package's one OPEN row, prior_trust_value_all_nested_open:
      Q nested → ∀ π ∈ Δ, Trust π (Q.toFrame) → Value π (Q.toFrame).
    WLOG the deferrer has full support (restricting to supp π gives a prior frame on fewer
    worlds with the same rows at support worlds and the same Trust/Value verdicts), and Trust
    of a full-support deferrer forces the evidence to be factive (F14's argument with π in place
    of μ) and mass-monotone (`PriorFrame.mass_Ev_le_of_mem_of_simpleTrust`'s argument, which is
    independent of the deferrer's values), and on nested maps mass-monotone + factive is
    transitive (`PriorFrame.Ev_subset_of_mem_of_nested`'s argument), so the search runs over
    evidence maps that are factive, transitive and nested — the reflexive-transitive relations w R v :⟺ v ∈ E_w whose
    value family is laminar.
(b) The report's "natural converse question" (E1, not attempted): does Total Trust of the
    prior force nested evidence?  Search factive + transitive + NON-nested maps for a prior μ
    with Value μ (decided through Theorem 4.1 / frames' tfae_value: hull condition + guarded
    modest informedness of every candidate).  The audit's argument says there is none.
(c) Sanity over ALL 15^4 evidence maps with two priors: every (E, μ) with Value μ is nested.

Trust is decided at attained thresholds (loses nothing: for fixed (q, p) the event
[P(q|p) ≥ t] is constant between attained values and the inequality at a smaller t with the
same event is implied).  Hull membership in the 3-simplex is decided exactly by Carathéodory:
a point of the hull of a finite set lies in the hull of ≤ 4 affinely independent points, for
which the barycentric system has a unique solution.

This is a search, not a proof.
"""
from fractions import Fraction as Fr
from itertools import product, combinations
import sys
import time

W = (0, 1, 2, 3)
N = len(W)
SUBSETS = [frozenset(s) for r in range(0, N + 1) for s in combinations(W, r)]
NONEMPTY = [s for s in SUBSETS if s]


def mass(rho, q):
    return sum(rho[w] for w in q)


def cond(mu, E):
    m = mass(mu, E)
    return tuple(mu[v] / m if v in E else Fr(0) for v in W)


def solve_unique(A, b):
    """Exact RREF of the m×k system A λ = b. Returns λ if the solution exists and is unique,
    else None (inconsistent, or rank < k)."""
    m, k = len(A), len(A[0])
    M = [list(A[i]) + [b[i]] for i in range(m)]
    row = 0
    pivots = []
    for col in range(k):
        piv = next((r for r in range(row, m) if M[r][col] != 0), None)
        if piv is None:
            continue
        M[row], M[piv] = M[piv], M[row]
        pv = M[row][col]
        M[row] = [x / pv for x in M[row]]
        for r in range(m):
            if r != row and M[r][col] != 0:
                f = M[r][col]
                M[r] = [M[r][c] - f * M[row][c] for c in range(k + 1)]
        pivots.append(col)
        row += 1
        if row == m:
            break
    if len(pivots) < k:
        return None
    for r in range(row, m):
        if M[r][k] != 0:
            return None
    sol = [Fr(0)] * k
    for i, col in enumerate(pivots):
        sol[col] = M[i][k]
    return sol


def in_hull(x, pts):
    pts = list(set(pts))
    if x in pts:
        return True
    for k in range(2, N + 1):
        for S in combinations(pts, k):
            A = [[p[i] for p in S] for i in range(N)] + [[Fr(1)] * k]
            b = list(x) + [Fr(1)]
            sol = solve_unique(A, b)
            if sol is not None and all(s >= 0 for s in sol):
                return True
    return False


def frame_rows(mu, Ev):
    return [cond(mu, Ev[w]) for w in W]


def cell(rows, rho):
    return frozenset(w for w in W if rows[w] == rho)


def cands(rows, pi):
    return list({rows[w] for w in W if pi[w] > 0})


def simple_trust(pi, rows):
    for q in NONEMPTY:
        attained = sorted({mass(rows[w], q) for w in W})
        for t in attained:
            if t <= 0:
                continue
            A = frozenset(w for w in W if t <= mass(rows[w], q))
            mA = mass(pi, A)
            if mA > 0 and not (t * mA <= mass(pi, q & A)):
                return False
    return True


def trust(pi, rows):
    for q in NONEMPTY:
        for p in NONEMPTY:
            attained = sorted({mass(rows[w], q & p) / mass(rows[w], p)
                               for w in W if mass(rows[w], p) > 0})
            for t in attained:
                if t <= 0:
                    continue
                E = frozenset(w for w in W
                              if mass(rows[w], p) > 0 and t * mass(rows[w], p) <= mass(rows[w], q & p))
                pE = p & E
                mB = mass(pi, pE)
                if mB > 0 and not (t * mB <= mass(pi, q & pE)):
                    return False
    return True


def informed(rows, rho):
    c = cell(rows, rho)
    m = mass(rho, c)
    if m == 0:
        return None
    return tuple(rho[w] / m if w in c else Fr(0) for w in W)


def value(pi, rows):
    C = cands(rows, pi)
    if not in_hull(pi, C):
        return False
    for rho in C:
        ih = informed(rows, rho)
        if ih is None:
            return False
        Cminus = [s for s in cands(rows, rho) if s != rho]
        if not in_hull(rho, [ih] + Cminus):
            return False
    return True


def factive(Ev):
    return all(w in Ev[w] for w in W)


def transitive(Ev):
    return all(all(Ev[v] <= Ev[w] for v in Ev[w]) for w in W)


def nested(Ev):
    return all((a <= b) or (b <= a) or not (a & b) for a in Ev for b in Ev)


def compositions(n, parts, positive):
    lo = 1 if positive else 0
    out = []
    for c in product(range(lo, n + 1), repeat=parts):
        if sum(c) == n:
            out.append(tuple(Fr(x, n) for x in c))
    return out


def fmt(Ev):
    return tuple(tuple(sorted(s)) for s in Ev)


PRIORS = sorted(set(sum((compositions(n, N, True) for n in (4, 5, 6)), [])))
DEFERRERS = sorted(set(sum((compositions(n, N, True) for n in (4, 5, 6, 8)), [])))
ALL_MAPS = list(product(NONEMPTY, repeat=N))
PREORDERS = [Ev for Ev in ALL_MAPS if factive(Ev) and transitive(Ev)]
NESTED_PRE = [Ev for Ev in PREORDERS if nested(Ev)]
NONNESTED_PRE = [Ev for Ev in PREORDERS if not nested(Ev)]
print(f"evidence maps: {len(ALL_MAPS)}; factive+transitive: {len(PREORDERS)}; "
      f"of which nested: {len(NESTED_PRE)}, non-nested: {len(NONNESTED_PRE)}")
print(f"priors: {len(PRIORS)}; deferrers (full support): {len(DEFERRERS)}")
sys.stdout.flush()

t0 = time.time()
# (a) the OPEN row on nested frames
checked = 0
simple_only = 0
trust_pi = 0
counter_a = []
for Ev in NESTED_PRE:
    for mu in PRIORS:
        rows = frame_rows(mu, Ev)
        assert value(mu, rows), ("nested theorem violated?!", fmt(Ev), mu)
        for pi in DEFERRERS:
            checked += 1
            if not simple_trust(pi, rows):
                continue
            simple_only += 1
            v = value(pi, rows)
            if v:
                continue
            if trust(pi, rows):
                counter_a.append((fmt(Ev), mu, pi))
print(f"(a) nested frames: (E, mu, pi) triples {checked}; Simple Trust pi holds on {simple_only}; "
      f"Trust pi and not Value pi: {len(counter_a)}   [{time.time() - t0:.0f}s]")
for c in counter_a[:10]:
    print("   COUNTER (a):", c)
sys.stdout.flush()

# (b) converse on factive+transitive non-nested frames: any prior with Value?
t0 = time.time()
hits_b = []
checked_b = 0
for Ev in NONNESTED_PRE:
    for mu in PRIORS:
        checked_b += 1
        rows = frame_rows(mu, Ev)
        if value(mu, rows):
            hits_b.append((fmt(Ev), mu))
print(f"(b) factive+transitive NON-nested frames: (E, mu) pairs {checked_b}; "
      f"with Value mu (= Total Trust mu): {len(hits_b)}   [{time.time() - t0:.0f}s]")
for c in hits_b[:10]:
    print("   HIT (b):", c)
sys.stdout.flush()

# (c) sanity over all maps, two priors: Value mu implies nested (and factive, transitive)
t0 = time.time()
TWO = [tuple(Fr(1, 4) for _ in W), (Fr(1, 10), Fr(2, 10), Fr(3, 10), Fr(4, 10))]
val_c = 0
bad_c = []
for Ev in ALL_MAPS:
    for mu in TWO:
        rows = frame_rows(mu, Ev)
        if value(mu, rows):
            val_c += 1
            if not (nested(Ev) and factive(Ev) and transitive(Ev)):
                bad_c.append((fmt(Ev), mu))
print(f"(c) all maps x 2 priors: Value mu holds on {val_c} pairs; "
      f"of which NOT (nested and factive and transitive): {len(bad_c)}   [{time.time() - t0:.0f}s]")
for c in bad_c[:10]:
    print("   BAD (c):", c)
