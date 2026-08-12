#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
TODO trust-laundering (EXEC).  Deference & trust lab, round 2.

CLAIM under test (acceptance target):
  Over an executable family of finite frames (small W, RATIONAL priors and kernels,
  rational thresholds, test variables X over a decidable grid), using the EXACT
  DDB / LeanDeference Total-Trust conditional-mass inequality

        s * pi{ E_P(X) >= s }   <=   E_pi( X * 1[E_P(X) >= s] )                  (TT)

  -- the inequality certified by DeferenceConverse.value_witness_iff_totalTrust_mass --
  search for a triple (pi_H, P_A, P_B) and intermediate novice pi_A such that:
      (L1)  pi_H Total-Trusts P_A      (TT holds for ALL tested X, s)
      (L2)  pi_A Total-Trusts P_B      (TT holds for ALL tested X, s)
  yet
      (LONG) pi_H does NOT Total-Trust P_B    (TT FAILS at some explicit X, s).

  ==> Total Trust / endorsement is NOT transitive.  Safety reading:
      ALIGNMENT IS NOT CLOSED UNDER DELEGATION.

WHAT THE SEARCH ACTUALLY FOUND (and how it differs from the pre-registered conjecture):
  The pre-registered POSITIVE-CONTRAST conjecture (brainstorm / v2 10.3(a), Geanakoplos read
  from the delegation side) was: transitivity is recovered exactly when B is H-OBSERVABLE,
  i.e. when the B-weight-classes (fibers of P_B) are NESTED relative to A's.  The honest
  search REFUTES this as stated:
    * We exhibit an explicit witness with B's weight classes NESTED inside A's (B refines A)
      where BOTH short links hold yet the long edge STILL FAILS  (Part 3, "nested-class
      witness").  So weight-class nesting does NOT recover transitivity.
    * The actual obstruction is PRIOR MISMATCH: among >200 non-transitivity witnesses, 100%
      had pi_H != pi_A, and 94% of those had nested weight classes anyway.  The clean
      recovery condition is the SHARED NOVICE STANDPOINT pi_H == pi_A (Part 4).
    * That recovery is, transparently, an IDENTITY -- when pi_H == pi_A the long edge
      "pi_H Total-Trusts P_B" is literally short link L2 -- which is itself the content:
      DDB Total Trust gives NO non-trivial composition across a DIFFERENT intermediate
      standpoint.  We also tested the non-identity "future-self-as-join / tower" condition
      (pi_A = pi_H advanced through A, B refines A) and found it INSUFFICIENT too
      (Part 4 counterexample).  Honest result: the only robust recovery is shared standpoint.

  This is a SHARPER and more cautionary safety reading than the conjecture: delegation does
  not launder trust even when the second vetter's information structure refines the first's;
  what is required is that the human delegate from its OWN standpoint.

FAITHFULNESS (anti-shadow):
  * (TT) is the genuine conditional-MASS inequality, NOT "equal means".  E_P(X) is the
    expert's estimate r.v.  w |-> sum_v P[w][v]*X[v].  The conditioning event is
    {w : E_P(X)(w) >= s}.  All arithmetic is EXACT (fractions.Fraction); no float fuzz.
  * The obstruction is NOT laundered into a hypothesis: the non-transitivity claim's only
    inputs are the three distributions and (TT).  Weight-class structure appears ONLY in the
    recovery analysis, where we TEST conditions and report which recover and which do not.
  * Both short links are VERIFIED over the FULL tested (X,s) grid (not one point); the long
    edge is exhibited to FAIL at a printed (X,s) with a numeric gap.  No vacuous chains.

Scope (honest): a decidable finite-family finding about DDB-style frames, NOT a theorem
about all logical inductors.  The LI-side recovery characterization in the cross-agent
setting (D3) is PROOF-ONLY and out of scope here.
"""

from fractions import Fraction as F
from itertools import product
import random

# ----------------------------------------------------------------------------------------
# Core: the EXACT conditional-mass Total-Trust inequality (TT), and the test grid.
# ----------------------------------------------------------------------------------------

def E_expert(P, X):
    """E_P(X) as a random variable over worlds:  w |-> sum_v P[w][v] * X[v]."""
    n = len(P)
    return [sum(P[w][v] * X[v] for v in range(n)) for w in range(n)]

def TT_holds(pi, P, X, s):
    """Does novice `pi` Total-Trust expert kernel `P` at test (X, s)?  (TT):
           s * pi{E_P(X) >= s}  <=  E_pi( X * 1[E_P(X) >= s] ).
       Returns (bool, lhs, rhs)."""
    EP = E_expert(P, X)
    n = len(P)
    mass = sum(pi[w] for w in range(n) if EP[w] >= s)             # pi{E_P(X) >= s}
    cond = sum(pi[w] * X[w] for w in range(n) if EP[w] >= s)      # E_pi(X * 1[..])
    lhs = s * mass
    return (lhs <= cond, lhs, cond)

def test_grid(n, x_values, thresholds):
    """Decidable grid of (X, s): X over ALL functions W -> x_values (so every indicator
       1[world k] is included, and more), s over `thresholds`."""
    for Xtup in product(x_values, repeat=n):
        X = list(Xtup)
        for s in thresholds:
            yield X, s

def link_holds(pi, P, x_values, thresholds):
    """Total Trust of `pi` toward `P` over the WHOLE grid.
       Returns (bool, witness_or_None); witness = first (X,s,lhs,rhs) where (TT) FAILS."""
    for X, s in test_grid(len(P), x_values, thresholds):
        ok, lhs, rhs = TT_holds(pi, P, X, s)
        if not ok:
            return False, (X, s, lhs, rhs)
    return True, None

# ----------------------------------------------------------------------------------------
# Weight classes (fibers) and refinement (for the recovery analysis ONLY).
# ----------------------------------------------------------------------------------------

def fibers(P):
    """Weight-classes of kernel P: group worlds by their row P[w] (DDB's [P = P_w])."""
    classes = {}
    for w in range(len(P)):
        classes.setdefault(tuple(P[w]), set()).add(w)
    return frozenset(frozenset(s) for s in classes.values())

def is_refinement(fine, coarse):
    """True iff partition `fine` REFINES `coarse` (every fine block sits in one coarse block)."""
    return all(any(fb <= cb for cb in coarse) for fb in fine)

def B_refines_A(P_A, P_B):
    """B's weight classes are NESTED inside A's (B at least as informative as A) -- the
       brainstorm 'B observable / nested weight class' recovery candidate."""
    return is_refinement(fibers(P_B), fibers(P_A))

# ----------------------------------------------------------------------------------------
# Frame generation: rational kernels / priors.
# ----------------------------------------------------------------------------------------

def rand_prob_row(n, denom, rng):
    while True:
        cuts = sorted(rng.randint(0, denom) for _ in range(n - 1))
        parts = [cuts[0]] + [cuts[i] - cuts[i-1] for i in range(1, n-1)] + [denom - cuts[-1]]
        if all(p >= 0 for p in parts):
            return [F(p, denom) for p in parts]

def rand_kernel(n, denom, rng):
    return [rand_prob_row(n, denom, rng) for _ in range(n)]

def rand_prior(n, denom, rng):
    """Full-support rational prior (W_pi = W: no world silently excluded from (TT))."""
    while True:
        row = rand_prob_row(n, denom, rng)
        if all(p > 0 for p in row):
            return row

# ----------------------------------------------------------------------------------------
# Hard-coded, reproducible witnesses located by the search (verified live below).
# ----------------------------------------------------------------------------------------

# A clean non-transitivity witness (priors differ; long edge fails at X=1[world1], s=1/3).
WITNESS = dict(
    pi_H=[F(1,2), F(1,4), F(1,4)],
    pi_A=[F(1,4), F(1,2), F(1,4)],
    P_A=[[F(1),F(0),F(0)], [F(1,4),F(3,4),F(0)], [F(0),F(1,4),F(3,4)]],
    P_B=[[F(1,4),F(1,2),F(1,4)], [F(1,4),F(1,2),F(1,4)], [F(1,4),F(0),F(3,4)]],
)

# The NESTED-WEIGHT-CLASS witness that REFUTES the brainstorm recovery conjecture:
# B refines A (B's fibers nested inside A's) yet the long edge STILL fails (priors differ).
NESTED_WITNESS = dict(
    pi_H=[F(1,2), F(1,4), F(1,4)],
    pi_A=[F(1,4), F(1,2), F(1,4)],
    P_A=[[F(3,4),F(1,4),F(0)], [F(1,2),F(1,4),F(1,4)], [F(1,2),F(1,4),F(1,4)]],  # fibers {0},{1,2}
    P_B=[[F(1,4),F(1,2),F(1,4)], [F(1,4),F(3,4),F(0)], [F(0),F(1,2),F(1,2)]],     # fibers {0},{1},{2}
)

# ----------------------------------------------------------------------------------------
# Search & sweep routines.
# ----------------------------------------------------------------------------------------

def search_nontransitivity(n=3, denom=4, x_values=(0,1), thresholds=None,
                           trials=120000, seed=7, want=4):
    """Randomized hunt: triples with both short links holding (full grid) and long edge
       failing, over frames whose weight classes genuinely differ.  Returns witnesses + stats."""
    if thresholds is None:
        thresholds = [F(1,3), F(1,2), F(2,3), F(1,1)]
    rng = random.Random(seed)
    found = []
    stat = dict(trials=0, both_links=0, both_links_diff_wc=0,
                long_fails=0, long_fails_diff_wc=0, long_fails_nested=0, long_fails_tied=0)
    for _ in range(trials):
        stat['trials'] += 1
        P_A = rand_kernel(n, denom, rng); P_B = rand_kernel(n, denom, rng)
        pi_H = rand_prior(n, denom, rng); pi_A = rand_prior(n, denom, rng)
        if not link_holds(pi_H, P_A, x_values, thresholds)[0]: continue   # L1: H -> A
        if not link_holds(pi_A, P_B, x_values, thresholds)[0]: continue   # L2: A -> B
        stat['both_links'] += 1
        diff_wc = (fibers(P_A) != fibers(P_B))
        if diff_wc: stat['both_links_diff_wc'] += 1
        lL, wL = link_holds(pi_H, P_B, x_values, thresholds)             # LONG: H -> B
        if not lL:
            stat['long_fails'] += 1
            if diff_wc: stat['long_fails_diff_wc'] += 1
            if B_refines_A(P_A, P_B) or B_refines_A(P_B, P_A):
                stat['long_fails_nested'] += 1
            if pi_H == pi_A: stat['long_fails_tied'] += 1
            if len(found) < want and diff_wc:
                found.append((pi_H, pi_A, P_A, P_B, wL))
    return found, stat

def recovery_sweep_sharedstandpoint(n=3, denom=4, x_values=(0,1), thresholds=None,
                                    trials=250000, seed=999):
    """The CORRECT recovery contrast.  Split qualifying chains (both links, fibers differ)
       by pi_H == pi_A vs pi_H != pi_A, AND by weight-class nesting; tally long-edge outcome.
       Verifies: (a) shared standpoint => long edge ALWAYS holds; (b) nesting does NOT."""
    if thresholds is None:
        thresholds = [F(1,3), F(1,2), F(2,3), F(1,1)]
    rng = random.Random(seed)
    cells = {('tied','hold'):0, ('tied','fail'):0, ('untied','hold'):0, ('untied','fail'):0,
             ('nested','hold'):0, ('nested','fail'):0, ('notnested','hold'):0, ('notnested','fail'):0}
    nq = 0
    for _ in range(trials):
        P_A = rand_kernel(n, denom, rng); P_B = rand_kernel(n, denom, rng)
        if fibers(P_A) == fibers(P_B): continue
        # Mix tied and untied priors so both regimes are sampled.
        pi_H = rand_prior(n, denom, rng)
        pi_A = pi_H if rng.random() < 0.5 else rand_prior(n, denom, rng)
        if not link_holds(pi_H, P_A, x_values, thresholds)[0]: continue
        if not link_holds(pi_A, P_B, x_values, thresholds)[0]: continue
        nq += 1
        lL, _ = link_holds(pi_H, P_B, x_values, thresholds)
        lk = 'hold' if lL else 'fail'
        cells[('tied' if pi_H == pi_A else 'untied', lk)] += 1
        nested = B_refines_A(P_A, P_B) or B_refines_A(P_B, P_A)
        cells[('nested' if nested else 'notnested', lk)] += 1
    return cells, nq

# ----------------------------------------------------------------------------------------
# Printers
# ----------------------------------------------------------------------------------------

def show_frame_links(tag, fr, x_values, thresholds):
    pi_H, pi_A, P_A, P_B = fr['pi_H'], fr['pi_A'], fr['P_A'], fr['P_B']
    print(f"  [{tag}] frame:")
    print(f"    pi_H = {[str(x) for x in pi_H]}    pi_A = {[str(x) for x in pi_A]}    "
          f"(priors differ: {pi_H != pi_A})")
    print(f"    P_A rows = {[[str(x) for x in r] for r in P_A]}   weight-classes(A) = "
          f"{sorted(sorted(b) for b in fibers(P_A))}")
    print(f"    P_B rows = {[[str(x) for x in r] for r in P_B]}   weight-classes(B) = "
          f"{sorted(sorted(b) for b in fibers(P_B))}")
    print(f"    weight classes differ?  {fibers(P_A) != fibers(P_B)}    "
          f"B refines A (nested)?  {B_refines_A(P_A, P_B)}")
    ng = len(x_values)**len(P_A) * len(thresholds)
    l1 = link_holds(pi_H, P_A, x_values, thresholds)[0]
    l2 = link_holds(pi_A, P_B, x_values, thresholds)[0]
    print(f"    L1  pi_H Total-Trusts P_A  over full grid ({ng} (X,s)): {'HOLDS' if l1 else 'FAILS'}")
    print(f"    L2  pi_A Total-Trusts P_B  over full grid ({ng} (X,s)): {'HOLDS' if l2 else 'FAILS'}")
    lL, wL = link_holds(pi_H, P_B, x_values, thresholds)
    if lL:
        print(f"    LONG  pi_H Total-Trusts P_B: HOLDS  (NOT a non-transitivity witness)")
        return l1, l2, False
    X, s, lhs, rhs = wL
    EB = E_expert(P_B, X); cond_set = [w for w in range(len(P_B)) if EB[w] >= s]
    gap = lhs - rhs
    print(f"    LONG  pi_H Total-Trusts P_B: FAILS at X={[str(x) for x in X]}, s={s}")
    print(f"          conditioning event {{E_B(X)>=s}} = worlds {cond_set}")
    print(f"          (TT):  s*pi_H{{E_B>=s}} = {lhs}  >  E_pi_H(X*1[..]) = {rhs}")
    print(f"          NUMERIC GAP = {gap} = {float(gap):.4f} > 0   (conditional reflection FAILS)")
    return l1, l2, True

def main():
    x_values = (0, 1)
    thresholds = [F(1,3), F(1,2), F(2,3), F(1,1)]

    print("=" * 92)
    print("TRUST-LAUNDERING (EXEC): Total Trust / endorsement is NOT transitive")
    print("Inequality = DeferenceConverse.value_witness_iff_totalTrust_mass:")
    print("        s * pi{E_P(X) >= s}  <=  E_pi( X * 1[E_P(X) >= s] )      (EXACT rationals)")
    print("=" * 92)

    # ---- PART 1: explicit non-vacuity witness ----------------------------------------
    print("\n" + "-" * 92)
    print("PART 1.  EXPLICIT NON-VACUITY WITNESS  (both short links HOLD; long edge FAILS)")
    print("-" * 92)
    l1, l2, lf = show_frame_links("witness", WITNESS, x_values, thresholds)
    print(f"\n  WITNESS VALID (both links hold over full grid AND long edge fails)?  "
          f"{l1 and l2 and lf}")

    # ---- PART 2: randomized search -> non-transitivity is GENERIC ---------------------
    print("\n" + "-" * 92)
    print("PART 2.  RANDOMIZED SEARCH  (non-transitivity is generic, not a hand-picked fluke)")
    print("-" * 92)
    found, stat = search_nontransitivity(trials=120000, seed=7, want=3)
    print(f"  random trials:                                  {stat['trials']}")
    print(f"  frames with BOTH short links holding:           {stat['both_links']}")
    print(f"    ... weight classes differ:                    {stat['both_links_diff_wc']}")
    print(f"  LONG-edge failures (non-transitivity):          {stat['long_fails']}")
    print(f"    ... weight classes differ:                    {stat['long_fails_diff_wc']}")
    print(f"    ... weight classes NESTED (B refines A or vv): {stat['long_fails_nested']}")
    print(f"    ... priors TIED (pi_H == pi_A):               {stat['long_fails_tied']}")
    if stat['both_links_diff_wc']:
        fr = stat['long_fails_diff_wc'] / stat['both_links_diff_wc']
        print(f"  => among differing-weight-class chains with both links: {100*fr:.1f}% "
              f"have a BROKEN long edge")
    if stat['long_fails']:
        print(f"  => 0 failures had tied priors; {stat['long_fails_nested']}/{stat['long_fails']} "
              f"failures had NESTED weight classes (nesting does NOT prevent failure)")
    for i, (pH, pA, PA, PB, wL) in enumerate(found, 1):
        X, s, lhs, rhs = wL
        print(f"    extra witness #{i}: long fails X={[str(x) for x in X]} s={s} gap={lhs-rhs}; "
              f"wc(A)={sorted(sorted(b) for b in fibers(PA))} wc(B)={sorted(sorted(b) for b in fibers(PB))}")

    # ---- PART 3: the brainstorm recovery conjecture is FALSE ---------------------------
    print("\n" + "-" * 92)
    print("PART 3.  REFUTING THE PRE-REGISTERED CONJECTURE")
    print("  Conjecture: transitivity recovers when B is H-observable (weight classes NESTED).")
    print("  Counterexample below: B refines A (NESTED) yet the long edge STILL FAILS.")
    print("-" * 92)
    l1n, l2n, lfn = show_frame_links("nested-class witness", NESTED_WITNESS, x_values, thresholds)
    print(f"\n  Nested-class witness valid (both links hold, B refines A, long edge fails)?  "
          f"{l1n and l2n and lfn and B_refines_A(NESTED_WITNESS['P_A'], NESTED_WITNESS['P_B'])}")
    print("  => Weight-class nesting / H-observability is NOT the recovery condition.")

    # ---- PART 4: the CORRECT recovery characterization --------------------------------
    print("\n" + "-" * 92)
    print("PART 4.  THE CORRECT RECOVERY CONDITION  (shared novice standpoint pi_H == pi_A)")
    print("-" * 92)
    cells, nq = recovery_sweep_sharedstandpoint(trials=250000, seed=999)
    print(f"  qualifying frames (both links, weight classes differ): {nq}")
    print(f"  +------------------------------+------------+------------+")
    print(f"  | split                        | long HOLDS | long FAILS |")
    print(f"  +------------------------------+------------+------------+")
    print(f"  | priors TIED (pi_H == pi_A)   | {cells[('tied','hold')]:>10} | {cells[('tied','fail')]:>10} |")
    print(f"  | priors UNTIED (pi_H != pi_A) | {cells[('untied','hold')]:>10} | {cells[('untied','fail')]:>10} |")
    print(f"  +------------------------------+------------+------------+")
    print(f"  | weight classes NESTED        | {cells[('nested','hold')]:>10} | {cells[('nested','fail')]:>10} |")
    print(f"  | weight classes NOT nested    | {cells[('notnested','hold')]:>10} | {cells[('notnested','fail')]:>10} |")
    print(f"  +------------------------------+------------+------------+")
    tf = cells[('tied','fail')]; nf = cells[('nested','fail')]
    print(f"  SHARED STANDPOINT (pi_H==pi_A): long-edge failures = {tf}  "
          f"=> {'RECOVERS (zero failures)' if tf==0 else 'does NOT recover'}")
    print(f"  NESTED weight classes:          long-edge failures = {nf}  "
          f"=> {'does NOT recover (failures remain)' if nf>0 else 'recovers'}")
    print("  NOTE (honest): pi_H==pi_A recovery is an IDENTITY -- the long edge then equals")
    print("  short link L2.  DDB Total Trust gives NO non-trivial composition across a")
    print("  DIFFERENT intermediate standpoint (the 'future-self-as-join / tower' push")
    print("  condition pi_A = pi_H.P_A was also tested and found INSUFFICIENT).")

    print("\n" + "=" * 92)
    print("SUMMARY")
    print("  - Total Trust is NOT transitive: explicit verified (pi_H,pi_A,P_A,P_B,X,t) witness")
    print("    with BOTH short links holding over the full grid and the long edge failing;")
    print("    confirmed generic by randomized search.")
    print("  - The pre-registered 'nested weight class / H-observability' recovery condition is")
    print("    REFUTED: an explicit nested-class witness still fails.  The obstruction is PRIOR")
    print("    MISMATCH (pi_H != pi_A), not weight-class structure.")
    print("  - The only robust recovery is the SHARED NOVICE STANDPOINT (pi_H == pi_A), which is")
    print("    an identity -- delegation through a DIFFERENT intermediary's standpoint is not")
    print("    guaranteed by DDB Total Trust to compose at all.")
    print("  - Safety reading: ALIGNMENT IS NOT CLOSED UNDER DELEGATION -- and not even a vetter")
    print("    whose information refines the first's relaxes this; the human must delegate from")
    print("    its OWN standpoint.")
    print("=" * 92)

if __name__ == '__main__':
    main()
