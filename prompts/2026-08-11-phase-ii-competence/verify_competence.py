"""Track I — principal competence: exact recomputation.

Stdlib only, exact rationals throughout (`fractions.Fraction`); no float is
constructed anywhere in this file.  Every constant asserted in `REPORT.md` is
recomputed here, and the four house-checker parameter sets are submitted to the
*unmodified* checker imported from `checkers/`.

Run:  python3 verify_competence.py            (fast; ~2 s)
      python3 verify_competence.py --slow     (adds the wider enumerations)
"""
from __future__ import annotations

import json
import os
import sys
from fractions import Fraction as Q
from itertools import product

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(os.path.dirname(_HERE))
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

from checkers import enumeration  # noqa: E402  the unmodified house checker

SLOW = "--slow" in sys.argv

_RESULTS: list[tuple[str, bool, str]] = []


def check(name: str, condition: bool, detail: str = "") -> None:
    _RESULTS.append((name, bool(condition), detail))


# --------------------------------------------------------------------------
# skeleton v1 objects, one decision index n
# --------------------------------------------------------------------------
# A model is (Omega, Pi, P, vplus, X, B) with
#   Omega = range(m), Pi = range(k) carrying its fixed linear order (v1 §1),
#   P[w]  exact rational masses summing to 1 (v1 §6),
#   vplus[w][p], X[w][p] exact rationals bounded by B (v1 §1, §2).


def argmax_least(row):
    """v1 §2: least maximizer in Pi's fixed order."""
    best = 0
    for p in range(1, len(row)):
        if row[p] > row[best]:
            best = p
    return best


def selection_J(vplus):
    return tuple(argmax_least(row) for row in vplus)


def margin(row):
    """gamma = v(J) - max_{p != J} v(p); zero at a tie.  Requires |Pi| >= 2."""
    j = argmax_least(row)
    return row[j] - max(row[p] for p in range(len(row)) if p != j)


def regret(vplus, X):
    """R(w) = max_p X(w,p) - X(w, J(w)).  Nonnegative with no hypothesis."""
    J = selection_J(vplus)
    return tuple(max(X[w]) - X[w][J[w]] for w in range(len(X)))


def V(P, X, sel):
    return sum((P[w] * X[w][sel[w]] for w in range(len(P))), Q(0))


def delta_all(P, vplus, X):
    """max over *all* selections of V(c), minus V(DELEGATE) = E_P[R]."""
    R = regret(vplus, X)
    return sum((P[w] * R[w] for w in range(len(P))), Q(0))


def delta_fixed(P, vplus, X):
    """max over the constant conducts FIXED[pi], minus V(DELEGATE)."""
    J = selection_J(vplus)
    base = V(P, X, J)
    k = len(X[0])
    return max(sum((P[w] * X[w][p] for w in range(len(P))), Q(0)) for p in range(k)) - base


def delta_partition(P, vplus, X, blocks):
    """max over G-measurable selections, minus V(DELEGATE)."""
    J = selection_J(vplus)
    base = V(P, X, J)
    k = len(X[0])
    total = Q(0)
    for block in blocks:
        total += max(sum((P[w] * X[w][p] for w in block), Q(0)) for p in range(k))
    return total - base


def pc0_level(vplus, X):
    """least eta with |vplus - X| <= eta pointwise (PC-0)."""
    return max(abs(vplus[w][p] - X[w][p]) for w in range(len(X)) for p in range(len(X[0])))


def pc0_L1_level(P, vplus, X):
    """least eta with E_P[max_p |vplus - X|] <= eta  (PC-0^1, i.e. Track C's (MV-M))."""
    return sum((P[w] * max(abs(vplus[w][p] - X[w][p]) for p in range(len(X[0])))
                for w in range(len(P))), Q(0))


def canonical_regrade(vplus):
    """Replace each v(w,.) by its rank vector.  Preserves the full ordering, hence
    J and every ordinal functional of vplus; destroys every cardinal one."""
    out = []
    for row in vplus:
        order = sorted(set(row))
        out.append(tuple(Q(order.index(x)) for x in row))
    return tuple(out)


# --------------------------------------------------------------------------
# domain generators for the exhaustive passes
# --------------------------------------------------------------------------

def tables(m, k, values):
    for flat in product(values, repeat=m * k):
        yield tuple(tuple(flat[w * k + p] for p in range(k)) for w in range(m))


def simplex_points(m, denominator):
    def parts(total, slots):
        if slots == 1:
            yield (total,)
            return
        for first in range(total + 1):
            for rest in parts(total - first, slots - 1):
                yield (first,) + rest
    for c in parts(denominator, m):
        yield tuple(Q(x, denominator) for x in c)


def partitions_of(m):
    """all set partitions of range(m), as tuples of tuples"""
    if m == 0:
        yield ()
        return
    for rest in partitions_of(m - 1):
        for i in range(len(rest)):
            yield rest[:i] + (rest[i] + (m - 1,),) + rest[i + 1:]
        yield rest + (((m - 1),),)


# --------------------------------------------------------------------------
# A. structural propositions, exhaustive over a declared domain
# --------------------------------------------------------------------------

def pass_A(m=2, k=2, values=(Q(-1), Q(0), Q(1)), values_X=None, B=Q(1),
           denominator=4):
    values_X = values if values_X is None else values_X
    Ps = list(simplex_points(m, denominator))
    parts = list(partitions_of(m))
    counts = dict(models=0, points=0)

    fail = {name: None for name in
            ("A0-nonneg", "A1-ladder", "A2-identity", "A3-collapse-le",
             "A4-pc0", "A5-pc0L1", "A6-pc4", "A7-ordinal", "A9-pc4-circular",
             "A10-pc5-sound", "A11-pc1-circular")}

    for vplus in tables(m, k, values):
        J = selection_J(vplus)
        Rv = None
        gam = tuple(margin(row) for row in vplus)
        vcanon = canonical_regrade(vplus)
        if selection_J(vcanon) != J:
            fail["A7-ordinal"] = ("regrade moved J", vplus)
        for X in tables(m, k, values_X):
            counts["models"] += 1
            Rv = regret(vplus, X)
            maxR = max(Rv)
            # A0: regret is nonnegative with no hypothesis
            if any(r < 0 for r in Rv):
                fail["A0-nonneg"] = (vplus, X)
            # A4: PC-0(eta) => R <= 2 eta pointwise
            eta0 = pc0_level(vplus, X)
            if maxR > 2 * eta0:
                fail["A4-pc0"] = (vplus, X, str(eta0), str(maxR))
            # A7: the conclusion is invariant under regrading vplus
            for P in Ps:
                counts["points"] += 1
                da = delta_all(P, vplus, X)
                df = delta_fixed(P, vplus, X)
                # A2: Delta over all selections is exactly E_P[R]
                if da != sum((P[w] * Rv[w] for w in range(m)), Q(0)):
                    fail["A2-identity"] = (vplus, X, P)
                # A1: the comparator ladder
                for blocks in parts:
                    dg = delta_partition(P, vplus, X, blocks)
                    if not (df <= dg <= da):
                        fail["A1-ladder"] = (vplus, X, P, blocks)
                # A3: Delta_all(P) <= max_w R(w) for every credence
                if da > maxR:
                    fail["A3-collapse-le"] = (vplus, X, P)
                # A5: PC-0^1(eta) => Delta_all <= 2 eta
                if da > 2 * pc0_L1_level(P, vplus, X):
                    fail["A5-pc0L1"] = (vplus, X, P)
                # A6: PC-4 leakage bound, at every attained gate
                for bar in sorted(set(gam)):
                    hi = [w for w in range(m) if gam[w] >= bar]
                    lo = [w for w in range(m) if gam[w] < bar]
                    eta4 = max([Rv[w] for w in hi], default=Q(0))
                    q = sum((P[w] for w in lo), Q(0))
                    if da > eta4 + 2 * B * q:
                        fail["A6-pc4"] = (vplus, X, P, str(bar))
                # A7: same J, same X, same P => same conclusion
                if delta_all(P, vcanon, X) != da or delta_fixed(P, vcanon, X) != df:
                    fail["A7-ordinal"] = (vplus, X, P)
                # A10: PC-5(gamma_bar, eta) => Delta_all <= 2 eta + 2 B q
                for bar in sorted(set(gam)):
                    hi = [w for w in range(m) if gam[w] >= bar]
                    lo = [w for w in range(m) if gam[w] < bar]
                    eta5 = max([max(abs(vplus[w][p] - X[w][p]) for p in range(k))
                                for w in hi], default=Q(0))
                    q = sum((P[w] for w in lo), Q(0))
                    if da > 2 * eta5 + 2 * B * q:
                        fail["A10-pc5-sound"] = (vplus, X, P, str(bar))

            # A11: PC-1^p is exactly the uniformised target --
            #      max_w R(w) == sup_P Delta_fixed(P).
            if maxR != max(delta_fixed(P, vplus, X) for P in Ps):
                fail["A11-pc1-circular"] = (vplus, X)
            # A9: PC-4^p is exactly the uniformised target with its leakage --
            #      max_{gamma >= bar} R(w) == max(0, sup_P [Delta_fixed(P) - 2B q(P)]).
            for bar in sorted(set(gam)):
                hi = [w for w in range(m) if gam[w] >= bar]
                lo = [w for w in range(m) if gam[w] < bar]
                lhs = max([Rv[w] for w in hi], default=Q(0))
                rhs = max([delta_fixed(P, vplus, X)
                           - 2 * B * sum((P[w] for w in lo), Q(0)) for P in Ps]
                          + [Q(0)])
                if lhs != rhs:
                    fail["A9-pc4-circular"] = (vplus, X, str(bar), str(lhs), str(rhs))

    for name, witness in fail.items():
        check(f"{name}", witness is None,
              "no counterexample" if witness is None else f"FAILED at {witness}")
    return counts


# A12: PC-0(eta) implies Track B's grade trust GT_G(eta) at every admissible
# conditioning partition (one refining the level sets of the grade profile).
def pass_A12(m=2, k=2, values=(Q(-1), Q(0), Q(1)), denominator=4):
    bad = None
    for vplus in tables(m, k, values):
        admissible = [blocks for blocks in partitions_of(m)
                      if all(vplus[a] == vplus[b] or a == b
                             for block in blocks for a in block for b in block)]
        for X in tables(m, k, values):
            eta = pc0_level(vplus, X)
            for P in simplex_points(m, denominator):
                for blocks in admissible:
                    for block in blocks:
                        mass = sum((P[w] for w in block), Q(0))
                        if mass == 0:
                            continue
                        for p in range(k):
                            cond = sum((P[w] * X[w][p] for w in block), Q(0)) / mass
                            if abs(cond - vplus[block[0]][p]) > eta:
                                bad = (vplus, X, P, blocks, p)
    check("A12-pc0-implies-grade-trust", bad is None,
          "PC-0(eta) => GT_G(eta) at every admissible G"
          if bad is None else f"FAILED at {bad}")


# A3 second half: the supremum over credences is attained at a point mass, so
# sup_P Delta_fixed(P) = sup_P Delta_all(P) = max_w R(w) exactly.
def pass_A3_attainment(m=2, k=2, values=(Q(-1), Q(0), Q(1))):
    bad = None
    for vplus in tables(m, k, values):
        for X in tables(m, k, values):
            R = regret(vplus, X)
            maxR = max(R)
            best_fix = None
            best_all = None
            for w in range(m):
                P = tuple(Q(1) if u == w else Q(0) for u in range(m))
                df, da = delta_fixed(P, vplus, X), delta_all(P, vplus, X)
                if df != R[w] or da != R[w]:
                    bad = ("point mass does not read off R", vplus, X, w)
                best_fix = df if best_fix is None else max(best_fix, df)
                best_all = da if best_all is None else max(best_all, da)
            if best_fix != maxR or best_all != maxR:
                bad = ("sup over point masses != max R", vplus, X)
    check("A3-collapse-attained", bad is None,
          "sup_P Delta_fixed = sup_P Delta_all = max_w R, at a point mass"
          if bad is None else f"FAILED at {bad}")


# A8: the margin is 2-Lipschitz in the sup norm on grades.
def pass_A8(k=3, values=(Q(-1), Q(0), Q(1), Q(2))):
    bad = None
    attained = False
    for v in product(values, repeat=k):
        for vhat in product(values, repeat=k):
            d = max(abs(a - b) for a, b in zip(v, vhat))
            gap = abs(margin(v) - margin(vhat))
            if gap > 2 * d:
                bad = (v, vhat)
            if d > 0 and gap == 2 * d:
                attained = True
    check("A8-margin-lipschitz", bad is None,
          "|gamma(v) - gamma(vhat)| <= 2 max_p |v - vhat|" if bad is None else f"FAILED at {bad}")
    check("A8-margin-lipschitz-attained", attained, "the constant 2 is attained")


# --------------------------------------------------------------------------
# B. named witnesses
# --------------------------------------------------------------------------

def witnesses():
    # W2: PC-1 holds at 0 while PC-0 fails at every level below B.
    B = Q(3)
    vplus = ((B, -B),)
    X = ((Q(0), Q(0)),)
    P = (Q(1),)
    check("W2-ordinal-not-cardinal",
          max(regret(vplus, X)) == 0 and pc0_level(vplus, X) == B
          and delta_all(P, vplus, X) == 0,
          f"R == 0, Delta_all == 0, least PC-0 level == {B}")

    # W3: PC-0's constant 2 is attained.
    eta = Q(1, 2)
    vplus = ((Q(0), Q(0)),)
    X = ((-eta, eta),)
    P = (Q(1),)
    check("W3-pc0-sharp",
          pc0_level(vplus, X) == eta and delta_all(P, vplus, X) == 2 * eta,
          f"PC-0 level {eta}, Delta_all {delta_all(P, vplus, X)} = 2*eta")

    # W4: the PC-4 family.  High-margin state has zero regret; the indecisive
    # state (a tie, gamma = 0) carries the full 2B, on mass q.
    B, q = Q(2), Q(1, 5)
    vplus = ((Q(0), Q(0)), (Q(1), Q(0)))       # w0: tie (gamma 0); w1: gamma 1
    X = ((-B, B), (Q(0), Q(0)))
    P = (q, 1 - q)
    gam = tuple(margin(r) for r in vplus)
    Rv = regret(vplus, X)
    da, df = delta_all(P, vplus, X), delta_fixed(P, vplus, X)
    check("W4-pc4-strictly-weaker",
          gam == (Q(0), Q(1)) and Rv == (2 * B, Q(0))
          and da == 2 * B * q and df == 2 * B * q and max(Rv) == 2 * B,
          f"PC-4(gamma_bar=1, eta=0) holds; PC-1 fails below 2B={2*B}; "
          f"Delta_all = Delta_fixed = {da} = 2Bq")

    # W4b: the leakage 2Bq is exactly attained across a range of q.
    ok = True
    for num in range(0, 11):
        qq = Q(num, 10)
        Pq = (qq, 1 - qq)
        if delta_all(Pq, vplus, X) != 2 * B * qq:
            ok = False
    check("W4b-leakage-attained", ok, "Delta_all == 2Bq at q in {0, 1/10, ..., 1}")

    # W5: the ordinal gate degenerates.  In a tie-free model {gamma > 0} = Omega,
    # so PC-4 with the ordinal gate "J is the unique maximizer" *is* PC-1.
    vplus = ((Q(1), Q(0)), (Q(0), Q(2)))
    gam = tuple(margin(r) for r in vplus)
    check("W5-ordinal-gate-degenerate", all(g > 0 for g in gam),
          "tie-free model: the ordinal gate admits every state, so PC-4-ordinal == PC-1")

    # W6: the value-of-information gap 2B(1 - 1/m), the exact price of a
    # hindsight comparator over the constant comparators, at Delta_fixed == 0.
    rows = []
    for m in range(2, 7):
        B = Q(1)
        Om, Pi = m, m
        vplus = tuple(tuple(Q(0) for _ in range(Pi)) for _ in range(Om))
        X = tuple(tuple(B if p == w else -B for p in range(Pi)) for w in range(Om))
        P = tuple(Q(1, m) for _ in range(m))
        da, df = delta_all(P, vplus, X), delta_fixed(P, vplus, X)
        rows.append((m, da, df, 2 * B * (1 - Q(1, m))))
    check("W6-value-of-information",
          all(da == target and df == 0 for _, da, df, target in rows),
          "Delta_fixed == 0 and Delta_all == 2B(1-1/m) at m = " +
          ", ".join(f"{m}:{da}" for m, da, _, _ in rows))

    # W6b: 2B(1-1/m) is the maximum of Delta_all - Delta_fixed at m = k = 2.
    best, arg = Q(-10), None
    for vplus in tables(2, 2, (Q(-1), Q(0), Q(1))):
        for X in tables(2, 2, (Q(-1), Q(0), Q(1))):
            for P in simplex_points(2, 4):
                gap = delta_all(P, vplus, X) - delta_fixed(P, vplus, X)
                if gap > best:
                    best, arg = gap, (vplus, X, P)
    check("W6b-voi-max-at-m2", best == Q(1),
          f"max (Delta_all - Delta_fixed) = {best} = 2B(1-1/2) at B = 1")

    # W7: PC-2 is invariant under modification at finitely many indices.
    # A single spike leaves every Cesaro limsup at 0 and the deficit at 2B.
    B, n0, N = Q(2), 7, 400
    seq = [Q(0)] * N
    seq[n0] = 2 * B
    cesaro = [sum(seq[:Nn], Q(0)) / Nn for Nn in range(n0 + 1, N + 1)]
    check("W7-pc2-spike",
          seq[n0] == 2 * B and cesaro[-1] == Q(2 * B, N) and all(c > 0 for c in cesaro)
          and cesaro[-1] < Q(1, 20),
          f"R_n = 0 except R_{n0} = 2B = {2*B}; Cesaro average at N={N} is "
          f"{cesaro[-1]} and tends to 0, while the deficit at n={n0} is {2*B}")

    # W8: PC-0^1 and PC-4 are incomparable.
    # (a) PC-0^1 small, PC-4 fails: the whole discrepancy sits on a decisive state
    #     of small mass.
    B, q = Q(2), Q(1, 10)
    vplus = ((Q(1), Q(0)), (Q(1), Q(0)))
    X = ((-B, B), (Q(1), Q(0)))
    P = (q, 1 - q)
    l1 = pc0_L1_level(P, vplus, X)
    Rv = regret(vplus, X)
    gams = tuple(margin(r) for r in vplus)
    check("W8a-L1-does-not-give-pc4",
          l1 == q * 3 and Rv == (2 * B, Q(0)) and all(g == 1 for g in gams),
          f"PC-0^1 level {l1}; every state decisive (gamma = 1); "
          f"regret {Rv[0]} = 2B at a decisive state, so PC-4(1, eta) fails below 2B")
    # (b) PC-4 holds at eta = 0, PC-0^1 is at the maximum.
    B = Q(2)
    vplus = ((Q(0), Q(0)),)
    X = ((-B, B),)
    P = (Q(1),)
    check("W8b-pc4-does-not-give-L1",
          margin(vplus[0]) == 0 and pc0_L1_level(P, vplus, X) == B,
          f"the single state is indecisive so PC-4(gamma_bar>0, 0) holds vacuously; "
          f"PC-0^1 level is {pc0_L1_level(P, vplus, X)} = B")

    # W10: PC-5 (margin-gated calibration) is *not* circular.  On a decisive
    # state the calibration error can be maximal while the regret is zero, so
    # PC-5's least level strictly exceeds the level of the target it buys.
    B = Q(3)
    vplus = ((Q(1), Q(0)),)          # gamma = 1, decisive
    X = ((Q(0), Q(0)),)
    P = (Q(1),)
    gated_calibration = max(abs(vplus[0][p] - X[0][p]) for p in range(2))
    check("W10-pc5-not-circular",
          margin(vplus[0]) == 1 and regret(vplus, X) == (Q(0),)
          and gated_calibration == 1 and delta_all(P, vplus, X) == 0,
          "on a decisive state: regret 0, so the uniformised target holds at 0, "
          f"while PC-5's least level is {gated_calibration} > 0")

    # W9: the certificate bridge {gamma < bar} subset {gamma_hat < bar + 2 eta}.
    v = (Q(3), Q(0))
    vhat = (Q(3) - Q(1, 2), Q(1, 2))
    check("W9-margin-bridge",
          margin(v) - margin(vhat) == 2 * max(abs(a - b) for a, b in zip(v, vhat)),
          f"gamma {margin(v)} vs gamma_hat {margin(vhat)}: the 2*eta gap is attained")


# --------------------------------------------------------------------------
# C. house-checker certificate parameter sets
# --------------------------------------------------------------------------

def certificates():
    """Each parameter set is handed to the unmodified `checkers.enumeration`.
    The checker generates the domain itself; nothing here enumerates."""
    out = {}

    # C1 -- the collapse inequality over every rational credence at denominator 8.
    # Fixed structure: Omega = {w0, w1}, Pi = {p0, p1}, B = 1,
    #   vplus = ((1,0),(0,1))  so J = (p0, p1);  X = ((-1,1),(1,-1)).
    # R = (2, 2), max R = 2.  For each pi the constraint
    #   sum_w P(w) (X(w,J(w)) - X(w,pi)) >= -max_w R(w)
    # is linear in P, and its conjunction is exactly Delta_fixed(P) <= max_w R.
    vplus = ((Q(1), Q(0)), (Q(0), Q(1)))
    X = ((Q(-1), Q(1)), (Q(1), Q(-1)))
    J = selection_J(vplus)
    R = regret(vplus, X)
    maxR = max(R)
    cons = []
    for p in range(2):
        cons.append({"coefficients": [str(X[w][J[w]] - X[w][p]) for w in range(2)],
                     "rhs": str(-maxR)})
    out["C1-collapse-upper-bound"] = {
        "reading": "Delta_fixed(P) <= max_w R(w) = 2 for every rational credence "
                   "at denominator 60",
        "params": {"domain": "rational-simplex", "dimension": 2, "denominator": 60,
                   "property": "satisfies-linear-constraints", "constraints": cons},
    }

    # C2 -- the PC-4 leakage bound over every rational credence at denominator 8.
    # W4's structure: w0 indecisive (gamma = 0) carrying regret 2B, w1 decisive
    # (gamma = 1) carrying regret 0; B = 2, gamma_bar = 1, eta = 0.  For each pi,
    #   sum_w P(w) [ X(w,J(w)) - X(w,pi) + 2B * 1{gamma(w) < gamma_bar} ] >= 0
    # is linear in P; the conjunction is Delta_fixed(P) <= eta + 2B P(gamma < 1).
    B = Q(2)
    vplus = ((Q(0), Q(0)), (Q(1), Q(0)))
    X = ((-B, B), (Q(0), Q(0)))
    J = selection_J(vplus)
    gam = tuple(margin(r) for r in vplus)
    cons = []
    for p in range(2):
        cons.append({"coefficients":
                     [str(X[w][J[w]] - X[w][p] + (2 * B if gam[w] < 1 else Q(0)))
                      for w in range(2)],
                     "rhs": "0"})
    out["C2-pc4-leakage"] = {
        "reading": "Delta_fixed(P) <= 0 + 2B * P(gamma < 1) for every rational "
                   "credence at denominator 60, with B = 2",
        "params": {"domain": "rational-simplex", "dimension": 2, "denominator": 60,
                   "property": "satisfies-linear-constraints", "constraints": cons},
    }

    # C3 -- PC-0(eta) => R <= 2 eta, over the whole X-box, at eta = 1/2 and
    # vplus = ((1,0),(0,1)).  Axis w,p runs over [vplus(w,p) - eta, vplus(w,p) + eta]
    # at denominator 4.  Constraints: for each w and each pi,
    #   X(w,J(w)) - X(w,pi) >= -2 eta.
    eta = Q(1, 2)
    vplus = ((Q(1), Q(0)), (Q(0), Q(1)))
    J = selection_J(vplus)
    den = 4
    axes = []
    for w in range(2):
        for p in range(2):
            lo = (vplus[w][p] - eta) * den
            hi = (vplus[w][p] + eta) * den
            axes.append({"low": int(lo), "high": int(hi)})
    cons = []
    for w in range(2):
        for p in range(2):
            coeff = [Q(0)] * 4
            coeff[w * 2 + J[w]] += 1
            coeff[w * 2 + p] -= 1
            cons.append({"coefficients": [str(c) for c in coeff], "rhs": str(-2 * eta)})
    out["C3-pc0-implies-regret"] = {
        "reading": "over the PC-0 box at eta = 1/2, R(w) <= 2 eta = 1 at every w",
        "params": {"domain": "rational-grid", "denominator": den, "axes": axes,
                   "property": "satisfies-linear-constraints", "constraints": cons},
    }

    # C4 -- PC-1 is not implied by the target at a fixed credence: with
    # P = (1/2, 1/2) fixed and the X-box of C3, no linear certificate is being
    # claimed; instead this set certifies the *necessity* direction by exhibiting
    # that every point of a declared lambda-grid violates the pointwise bound
    # when the model is W4's.  eta must be at least 2B = 4.
    out["C4-pc1-level-necessity"] = {
        "reading": "in W4's model every eta in [0, 15/4] fails the pointwise "
                   "regret bound R <= eta; the least admissible eta is 2B = 4",
        "params": {"domain": "rational-grid", "denominator": 4,
                   "axes": [{"low": 0, "high": 15}],
                   "property": "violates-at-least-one",
                   "constraints": [{"coefficients": ["1"], "rhs": "4"}]},
    }

    for name, entry in out.items():
        ok, detail = enumeration.check(entry["params"])
        check(f"house-checker {name}", ok, detail)
    return out


# --------------------------------------------------------------------------
# slow passes
# --------------------------------------------------------------------------

def slow_passes():
    # three interventions: grades over {-1,0,1}, quantities over {-1,1}
    counts = pass_A(m=2, k=3, values=(Q(-1), Q(0), Q(1)), values_X=(Q(-1), Q(1)),
                    B=Q(1), denominator=3)
    check("slow-A-2x3", True,
          f"|Omega|=2, |Pi|=3: {counts['models']} models, {counts['points']} "
          "model-credence points")
    # three states: grades over {-1,0,1}, quantities over {-1,1}
    counts = pass_A(m=3, k=2, values=(Q(-1), Q(0), Q(1)), values_X=(Q(-1), Q(1)),
                    B=Q(1), denominator=2)
    check("slow-A-3x2", True,
          f"|Omega|=3, |Pi|=2: {counts['models']} models, {counts['points']} "
          "model-credence points")


# --------------------------------------------------------------------------

def main() -> int:
    counts = pass_A()
    check("A-domain", True,
          f"{counts['models']} models (|Omega|=|Pi|=2, grades and quantities in "
          f"{{-1,0,1}}), {counts['points']} model-credence points at denominator 4")
    pass_A3_attainment()
    pass_A12()
    pass_A8()
    witnesses()
    certs = certificates()
    if SLOW:
        slow_passes()

    with open(os.path.join(_HERE, "certificates.json"), "w") as handle:
        json.dump(certs, handle, indent=2, sort_keys=True)

    width = max(len(name) for name, _, _ in _RESULTS)
    failed = 0
    for name, ok, detail in _RESULTS:
        status = "ok  " if ok else "FAIL"
        failed += 0 if ok else 1
        print(f"{status} {name.ljust(width)}  {detail}")
    print(f"\n{len(_RESULTS)} checks, {failed} failed")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
