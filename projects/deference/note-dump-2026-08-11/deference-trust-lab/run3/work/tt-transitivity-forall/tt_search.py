#!/usr/bin/env python3
"""
tt-transitivity-forall : EXEC pre-search (run3 TODO 4)

Exact-rational (fractions.Fraction) pre-search and decision procedure for the
genuine DDB / LeanDeference Total-Trust predicate

    TT(pi, P)  :<=>  for ALL X : W -> Q and ALL s : Q,
        s * pi{ w : E_w(X) >= s }  <=  E_pi( X * 1[E_w(X) >= s] )

where E_w(X) = sum_v P[w][v] * X[v]  (the statement form of
DeferenceConverse.value_witness_iff_totalTrust_mass, LeanDeference.lean L426-431).

THE QUANTIFIER IS EXACT, NOT SAMPLED.  TT(pi,P) fails iff for some nonempty
S subseteq W the homogeneous linear system in (X, s)

    E_w(X) - s >= 0        for w in S
    s - E_w(X) >  0        for w not in S          (event is exactly S)
    sum_{w in S} pi_w (s - X_w) > 0                (the TT mass is negative)

is feasible over Q.  Each system is decided EXACTLY by Fourier-Motzkin
elimination over the rationals (all constraints homogeneous with rational
coefficients; FM preserves rationality; a feasible system of rational strict/
non-strict homogeneous constraints has a rational solution, obtainable by FM
back-substitution).  No (X, s) grid appears anywhere in this file.

SUPERSESSION: run2/work/trust-laundering.{py,md} is POISONED (verdict SHADOW:
its "TT holds" certifications were a 32-point (X,s) indicator grid, and its
printed headline witness is a vacuous chain under this genuine predicate).
Nothing from it is cited or reused here; every number below is re-derived.

Parts:
  0. The designed frame (partition conditional-expectation experts) + the
     explicit long-edge failure witness, verified exactly.
  1. Exact FM decision procedure, sanity-checked against the kernel-checked
     AntiExpert frame of LeanDeference.lean (TT must FAIL there).
  2. The three edges of the chain decided exactly: both short links HOLD
     (matching the paper/Lean lemma: partition experts are totally trusted by
     their own prior), the long edge FAILS; the recovery frame HOLDS.
  3. Exact characterization check + exhaustive (non-sampled) family statistic:
     over ALL priors with denominator N on 3 worlds, long-edge failure is
     EXACTLY conditional-prior mismatch on some cell of F_B.  Includes the
     sharper-than-run2 witness: priors that DIFFER but agree conditionally on
     every F_B cell -> long edge HOLDS (prior identity is sufficient, not
     necessary; the exact lever is cellwise conditional agreement).
"""

from fractions import Fraction as Fr
from itertools import combinations, product
import sys

# ----------------------------------------------------------------------------
# Basic frame utilities
# ----------------------------------------------------------------------------

def cond_expert(pi, cells):
    """The pi-conditional-expectation expert of a partition.
    cells: list of lists partitioning range(n).
    Row w = pi conditioned on the cell containing w."""
    n = len(pi)
    cell_of = {}
    for C in cells:
        for w in C:
            cell_of[w] = tuple(C)
    P = [[Fr(0)] * n for _ in range(n)]
    for w in range(n):
        C = cell_of[w]
        mass = sum(pi[v] for v in C)
        assert mass > 0
        for v in C:
            P[w][v] = pi[v] / mass
    return P

def E_row(P, w, X):
    return sum(P[w][v] * X[v] for v in range(len(X)))

def tt_mass(pi, P, X, s):
    """The TT mass  sum_{w : E_w(X) >= s} pi_w (X_w - s).
    TT inequality at (X,s)  <=>  mass >= 0  (totalTrust_sum_split algebra)."""
    return sum(pi[w] * (X[w] - s) for w in range(len(pi)) if E_row(P, w, X) >= s)

# ----------------------------------------------------------------------------
# Exact Fourier-Motzkin feasibility for homogeneous strict/non-strict systems
# ----------------------------------------------------------------------------
# constraint = (coeffs tuple over variables, strict: bool) meaning
#   dot(coeffs, y) >= 0   (strict=False)   or   dot(coeffs, y) > 0  (strict=True)

def _normalize(c):
    """Scale so first nonzero coeff has absolute value with small height (dedup aid)."""
    coeffs, strict = c
    nz = [x for x in coeffs if x != 0]
    if not nz:
        return (tuple(Fr(0) for _ in coeffs), strict)
    g = abs(nz[0])
    return (tuple(x / g for x in coeffs), strict)

def fm_feasible(constraints, nvars):
    """Exact feasibility of the homogeneous system over Q (equivalently R)."""
    cons = set()
    for c in constraints:
        coeffs, strict = _normalize(c)
        if all(x == 0 for x in coeffs):
            if strict:
                return False        # 0 > 0
            continue                # 0 >= 0, drop
        cons.add((coeffs, strict))
    for k in range(nvars):          # eliminate variable k
        pos, neg, zero = [], [], []
        for coeffs, strict in cons:
            a = coeffs[k]
            if a > 0:
                pos.append((coeffs, strict))
            elif a < 0:
                neg.append((coeffs, strict))
            else:
                zero.append((coeffs, strict))
        new = set()
        for (a, sa) in pos:
            for (b, sb) in neg:
                # combined: a_k * b - b_k * a   (k-coeff cancels); strict iff either strict
                ak, bk = a[k], b[k]
                comb = tuple(ak * b[i] - bk * a[i] for i in range(len(a)))
                strict = sa or sb
                if all(x == 0 for x in comb):
                    if strict:
                        return False
                    continue
                new.add(_normalize((comb, strict)))
        cons = set()
        for coeffs, strict in zero:
            cons.add((coeffs, strict))
        cons |= new
        # after eliminating k, all constraints have coeff 0 at k by construction
    # all variables eliminated; any surviving constraint would be all-zero
    for coeffs, strict in cons:
        if all(x == 0 for x in coeffs) and strict:
            return False
    return True

def tt_holds_exact(pi, P):
    """EXACT decision of TT(pi, P) over ALL X : W -> Q, s : Q.
    Returns (True, None) or (False, S) where S is a feasible violating event."""
    n = len(pi)
    worlds = list(range(n))
    for r in range(1, n + 1):
        for S in combinations(worlds, r):
            Sset = set(S)
            cons = []
            for w in worlds:
                row = [P[w][v] for v in range(n)]
                if w in Sset:
                    cons.append((tuple(row + [Fr(-1)]), False))          # E_w - s >= 0
                else:
                    cons.append((tuple([-x for x in row] + [Fr(1)]), True))  # s - E_w > 0
            viol = [-pi[w] if w in Sset else Fr(0) for w in worlds]
            viol.append(sum(pi[w] for w in Sset))
            cons.append((tuple(viol), True))                             # mass < 0
            if fm_feasible(cons, n + 1):
                return (False, S)
    return (True, None)

# ----------------------------------------------------------------------------
# Characterization predicate and direct witness construction
# ----------------------------------------------------------------------------

def cond_mismatch(piH, piA, cells):
    """Exists a cell C of the partition and v0 in C with piA(v0|C) > piH(v0|C)?
    (By the pivot argument, some cell has DIFFERING conditionals iff some
    (cell, v0) has a strict > in this direction.)  Returns (cell, v0, sA, sH)
    for the first strict >, or None if conditionals agree on every cell."""
    for C in cells:
        mH = sum(piH[v] for v in C)
        mA = sum(piA[v] for v in C)
        for v0 in C:
            if piA[v0] / mA > piH[v0] / mH:
                return (tuple(C), v0, piA[v0] / mA, piH[v0] / mH)
    return None

def witness_from_mismatch(piH, piA, cells, mism):
    """X = indicator of v0, s = piA(v0|C).  Returns (X, s, mass)."""
    C, v0, sA, sH = mism
    n = len(piH)
    X = [Fr(1) if v == v0 else Fr(0) for v in range(n)]
    s = sA
    P = cond_expert(piA, cells)
    m = tt_mass(piH, P, X, s)
    return (X, s, m)

# ----------------------------------------------------------------------------
# Part 0: the designed frame
# ----------------------------------------------------------------------------

def frac_str(x):
    return str(x)

def show_matrix(P):
    return "[" + ", ".join("[" + ", ".join(frac_str(x) for x in row) + "]" for row in P) + "]"

def main():
    print("=" * 78)
    print("PART 0: designed frame and the explicit long-edge failure witness")
    print("=" * 78)

    piH = [Fr(1, 2), Fr(1, 4), Fr(1, 4)]
    piA = [Fr(1, 4), Fr(1, 2), Fr(1, 4)]
    FA = [[0], [1, 2]]          # partition F_A: cells {0}, {1,2}
    FB = [[0, 1], [2]]          # partition F_B: cells {0,1}, {2}
    PA = cond_expert(piH, FA)   # pi_H-conditional on F_A
    PB = cond_expert(piA, FB)   # pi_A-conditional on F_B  (NOT pi_H-conditional)
    PBrec = cond_expert(piH, FB)  # recovery: pi_H-conditional on F_B

    print(f"pi_H = {[frac_str(x) for x in piH]}   pi_A = {[frac_str(x) for x in piA]}")
    print(f"F_A = {FA}   F_B = {FB}   (non-nested, both non-trivial)")
    print(f"P_A  = condExpert(pi_H, F_A) = {show_matrix(PA)}")
    print(f"P_B  = condExpert(pi_A, F_B) = {show_matrix(PB)}")
    print(f"P_B' = condExpert(pi_H, F_B) = {show_matrix(PBrec)}   (recovery frame)")
    assert piH != piA, "priors must differ"
    assert PB != PBrec, "P_B must NOT be pi_H-conditional"
    print("checks: pi_A != pi_H  OK;  P_B != condExpert(pi_H, F_B)  OK")
    for P in (PA, PB, PBrec):
        for w in range(3):
            assert sum(P[w]) == 1
    print("checks: all expert rows sum to 1  OK")

    # explicit failure witness for the long edge, re-derived (not cited from run2):
    X0 = [Fr(0), Fr(1), Fr(0)]
    s0 = Fr(1, 2)
    Evals = [E_row(PB, w, X0) for w in range(3)]
    event = [w for w in range(3) if Evals[w] >= s0]
    lhs = s0 * sum(piH[w] for w in event)
    rhs = sum(piH[w] * X0[w] for w in event)
    mass = tt_mass(piH, PB, X0, s0)
    print(f"\nLong-edge witness: X = {[frac_str(x) for x in X0]}, s = {s0}")
    print(f"  E_w(X) under P_B = {[frac_str(e) for e in Evals]}   event {{E>=s}} = {event}")
    print(f"  TT inequality:  s*pi_H(event) = {lhs}  <=?  E_piH(X*1_event) = {rhs}")
    print(f"  TT mass = {mass}  (gap = {lhs - rhs})")
    assert mass == Fr(-1, 8) and lhs - rhs == Fr(1, 8)
    print("  => long edge FAILS at this (X,s); exact rational gap 1/8.  OK")

    print()
    print("=" * 78)
    print("PART 1: exact FM decision procedure; sanity check vs kernel-checked facts")
    print("=" * 78)
    # AntiExpert frame of LeanDeference.lean (L456-487): TT must FAIL
    # (TT_negative: mass -1/4 at X=1[world 0], s=1/2).
    pi_anti = [Fr(1, 2), Fr(1, 2)]
    P_anti = [[Fr(1, 5), Fr(4, 5)], [Fr(4, 5), Fr(1, 5)]]
    ok, S = tt_holds_exact(pi_anti, P_anti)
    print(f"AntiExpert frame (LeanDeference L456-487): TT decided {'HOLDS' if ok else 'FAILS'}"
          f"{'' if ok else f' (violating event {S})'}")
    assert not ok, "decision procedure must refute the kernel-checked anti-expert"
    # identity expert: TT must HOLD (P w = delta_w => event mass sums are trivial)
    P_id = [[Fr(1) if v == w else Fr(0) for v in range(2)] for w in range(2)]
    ok2, _ = tt_holds_exact(pi_anti, P_id)
    print(f"Identity expert on 2 worlds: TT decided {'HOLDS' if ok2 else 'FAILS'}")
    assert ok2
    print("sanity checks passed.")

    print()
    print("=" * 78)
    print("PART 2: the chain, decided EXACTLY (all X in Q^3, all s in Q)")
    print("=" * 78)
    okA, SA = tt_holds_exact(piH, PA)
    okB, SB = tt_holds_exact(piA, PB)
    okL, SL = tt_holds_exact(piH, PB)
    okR, SR = tt_holds_exact(piH, PBrec)
    print(f"L1   TT(pi_H, P_A)  : {'HOLDS (exactly decided, all X,s)' if okA else f'FAILS {SA}'}")
    print(f"L2   TT(pi_A, P_B)  : {'HOLDS (exactly decided, all X,s)' if okB else f'FAILS {SB}'}")
    print(f"LONG TT(pi_H, P_B)  : {'HOLDS' if okL else f'FAILS (violating event {SL})'}")
    print(f"REC  TT(pi_H, P_B') : {'HOLDS (exactly decided, all X,s)' if okR else f'FAILS {SR}'}")
    assert okA and okB and (not okL) and okR
    print("\n=> NON-TRANSITIVITY established at the exact predicate:")
    print("   both short links HOLD for ALL (X,s); the long edge FAILS;")
    print("   replacing pi_A by pi_H in P_B's construction restores the long edge.")

    print()
    print("=" * 78)
    print("PART 3: exact characterization + EXHAUSTIVE family statistic (no sampling)")
    print("=" * 78)
    print("""Paper claim (proved in the writeup, kernel-checked in the Lean file):
  for positive priors, TT(pi_H, condExpert(pi_A, F))  <=>
  pi_H(.|C) = pi_A(.|C) on EVERY cell C of F.
Cross-check the FM decision against this predicate over an exhaustive family.""")

    N = 6   # all priors with denominator N: numerators positive, summing to N
    priors = []
    for a in range(1, N - 1):
        for b in range(1, N - a):
            c = N - a - b
            priors.append([Fr(a, N), Fr(b, N), Fr(c, N)])
    parts3 = [[[0], [1, 2]], [[1], [0, 2]], [[2], [0, 1]]]  # nontrivial partitions of 3
    total = fails = holds_diff_prior = 0
    mism_agree = 0
    diag_fail = 0
    witnesses_checked = 0
    for FBx in parts3:
        for pH in priors:
            for pA in priors:
                P = cond_expert(pA, FBx)
                ok, S = tt_holds_exact(pH, P)
                mism = cond_mismatch(pH, pA, FBx)
                total += 1
                # characterization: TT holds <=> no conditional mismatch
                assert ok == (mism is None), (pH, pA, FBx, ok, mism)
                mism_agree += 1
                if not ok:
                    fails += 1
                    # verify the direct witness construction exactly
                    X, s, m = witness_from_mismatch(pH, pA, FBx, mism)
                    assert m < 0
                    witnesses_checked += 1
                if ok and pH != pA:
                    holds_diff_prior += 1
                if pH == pA and not ok:
                    diag_fail += 1
    n_priors = len(priors)
    print(f"family: all {n_priors} positive priors with denominator {N}, "
          f"all {n_priors}^2 ordered pairs, all 3 nontrivial partitions of 3 worlds")
    print(f"  total long-edge decisions           : {total}")
    print(f"  characterization agreement           : {mism_agree}/{total} (FM == cellwise-conditional test)")
    print(f"  long edge FAILS                      : {fails}  "
          f"({Fr(fails, total)} = {float(Fr(fails, total)):.4f} of the family)")
    print(f"  direct witnesses (X=delta_v0, s=piA(v0|C)) verified mass<0 : {witnesses_checked}/{fails}")
    print(f"  recovery (pi_A == pi_H) failures     : {diag_fail}  (theorem: must be 0)")
    print(f"  HOLDS with pi_A != pi_H              : {holds_diff_prior}  "
          f"(prior identity is SUFFICIENT but NOT NECESSARY)")
    assert diag_fail == 0

    # the sharper-than-run2 witness: differing priors, conditionals agree on F_B cells
    pH2 = [Fr(1, 6), Fr(1, 6), Fr(4, 6)]
    pA2 = [Fr(2, 6), Fr(2, 6), Fr(2, 6)]
    FB2 = [[0, 1], [2]]
    ok3, _ = tt_holds_exact(pH2, cond_expert(pA2, FB2))
    print(f"\nSharper witness: pi_H = {[frac_str(x) for x in pH2]}, "
          f"pi_A = {[frac_str(x) for x in pA2]}, F_B = {FB2}")
    print(f"  priors differ, but conditionals on {{0,1}} are (1/2,1/2) for both, "
          f"and on {{2}} trivially agree")
    print(f"  => TT(pi_H, condExpert(pi_A, F_B)) decided: {'HOLDS' if ok3 else 'FAILS'}")
    assert ok3
    print("  run2's slogan 'the obstruction is prior mismatch' is imprecise: the exact")
    print("  lever is CONDITIONAL mismatch on some cell of F_B.")

    # short links across the family: partition experts always trusted by own prior
    short_ok = 0
    short_total = 0
    for FBx in parts3:
        for p in priors:
            ok4, _ = tt_holds_exact(p, cond_expert(p, FBx))
            short_total += 1
            assert ok4
            short_ok += 1
    print(f"\nlemma-1 cross-check: TT(pi, condExpert(pi, F)) decided HOLDS for "
          f"{short_ok}/{short_total} (prior, partition) pairs in the family.")

    print("\nALL ASSERTIONS PASSED.")

if __name__ == "__main__":
    sys.exit(main())
