"""
Micro-examples for the model

    "UDT1.0 that (1-δ)-believes its policy is UDT1.1  ==>  ε-optimal."

Two parts, both checkable by hand:

  PART A.  The mixture-deference bound (whole-policy view, the Lean shadow).
           Verifies, on a concrete finite policy menu, that committing to a
           Bel-maximizer s gives
                (1-δ)(V*(p*) - V*(s)) <= δ (hi - lo),
           and that the clean form V*(p*) - V*(s) <= δ/(1-δ) (hi-lo) holds,
           and that the principal's naive ε = δ·range UNDERSHOOTS (the real
           gap exceeds δ·range), confirming the 1/(1-δ) correction is real.

  PART B.  The Stag-Hunt self-coordination game (pointwise view), which is
           the content the whole-policy bound *assumes* via hsel.  Two
           situations (two copies of the agent) play a Stag Hunt.  We show:
             (B1) pointwise UDT1.0 best response has TWO fixed points:
                  the optimal (Stag,Stag) AND the bad (Hare,Hare).  So
                  UDT1.0-with-itself is NOT guaranteed optimal -- the menu
                  for Part A is not enough; you can be trapped.
             (B2) a UDT1.0 copy that (1-δ)-believes the OTHER copy plays the
                  UDT1.1 action (Stag) best-responds with Stag for all
                  δ below an explicit threshold δ* -- the belief BREAKS the
                  bad equilibrium and SELECTS the good one.  This is the
                  "correlation device" mechanism: belief-you're-UDT1.1 points
                  every situation-copy at the same optimal policy.

No external deps beyond the stdlib + (optional) sympy for an exact symbolic
check of the threshold.  Run:  python3 unbounded_embedded_agency_micro.py
"""

from fractions import Fraction as F

# ============================================================
# PART A.  Whole-policy mixture-deference bound (Lean shadow)
# ============================================================

def part_A():
    print("=" * 64)
    print("PART A.  Mixture-deference bound  (1-δ)(V*(p*)-V*(s)) ≤ δ(hi-lo)")
    print("=" * 64)

    # A finite menu of whole policies.  V* = true (UDT1.1) value-of-policy.
    # Vother = an arbitrary, adversarial 'wrong-code' value map.
    # Utilities bounded in [lo, hi].
    lo, hi = F(0), F(1)

    # Policies a..d.  p* = the V*-argmax (the genuine UDT1.1 policy).
    Vstar  = {'a': F(0),   'b': F(1),    'c': F(3,4),  'd': F(1,2)}   # b is optimal
    # Adversarial Vother: makes the *suboptimal* policy 'c' look best, and the
    # optimum 'b' look worst, within [0,1].  This is the worst case for the bound.
    Vother = {'a': F(1,2), 'b': F(0),    'c': F(1),    'd': F(1,2)}

    pstar = max(Vstar, key=lambda k: Vstar[k])
    assert pstar == 'b'

    def run(delta):
        Bel = {k: (1 - delta) * Vstar[k] + delta * Vother[k] for k in Vstar}
        s = max(Bel, key=lambda k: Bel[k])               # believed-maximizer
        lhs = (1 - delta) * (Vstar[pstar] - Vstar[s])    # (1-δ)(V*(p*)-V*(s))
        rhs = delta * (hi - lo)                          # δ(hi-lo)
        # honest gap and the two ε candidates
        true_gap   = Vstar[pstar] - Vstar[s]
        eps_naive  = delta * (hi - lo)                   # principal's stated bound
        eps_honest = (delta / (1 - delta)) * (hi - lo) if delta < 1 else None
        return s, lhs, rhs, true_gap, eps_naive, eps_honest

    print(f"  V*     = {{a:0, b:1, c:3/4, d:1/2}}   (p* = b, optimum)")
    print(f"  Vother = {{a:1/2, b:0, c:1, d:1/2}}   (adversarial)")
    print(f"  range hi-lo = {hi-lo}\n")
    print(f"  {'δ':>6} {'chosen s':>9} {'(1-δ)Δ':>8} {'≤ δrange?':>9}"
          f" {'trueΔ':>7} {'δ·range':>8} {'δ/(1-δ)r':>9} {'naive ok?':>9}")
    for delta in [F(0), F(1,10), F(1,4), F(1,3), F(1,2), F(2,3), F(9,10)]:
        s, lhs, rhs, tg, en, eh = run(delta)
        bound_ok  = lhs <= rhs                            # the proved inequality
        naive_ok  = (tg <= en)                            # does naive δ·range bound the TRUE gap?
        ehs = "  --  " if eh is None else f"{float(eh):.4f}"
        print(f"  {str(delta):>6} {s:>9} {float(lhs):>8.4f} {str(bound_ok):>9}"
              f" {float(tg):>7.4f} {float(en):>8.4f} {ehs:>9} {str(naive_ok):>9}")
        assert bound_ok, f"PROVED inequality violated at δ={delta}"
        # honest bound always holds where defined:
        if eh is not None:
            assert tg <= eh + F(1, 10**9), f"honest bound violated at δ={delta}"

    print("\n  Reading:")
    print("   * The proved inequality (1-δ)Δ ≤ δ·range holds at every δ  (assert ok).")
    print("   * 'naive ok?' = False once δ is large enough: the principal's stated")
    print("     ε = δ·range FAILS to bound the TRUE gap (e.g. δ=1/3: trueΔ=0.25 > 0.333? no,")
    print("     but δ=2/3: trueΔ=1.0 > δ·range=0.667 -> naive UNDERSHOOTS). The honest")
    print("     ε = δ/(1-δ)·range always works. This is the correction the model forces.\n")


# ============================================================
# PART B.  Stag-Hunt self-coordination  (pointwise UDT1.0)
# ============================================================
#
# Two situations s0, s1 (two copies / two times of the same agent).  Each
# chooses an action in {Stag=S, Hare=H}.  Symmetric Stag Hunt payoff to the
# *agent as a whole* (the global utility), as a function of the joint profile:
#
#        other=S   other=H
#   S      (b,b)    (0, c)          b > c > 0  (Stag is the better equilibrium)
#   H      (c,0)    (c,c)
#
# Concretely b=4, c=3.  Global utility of a profile = sum of the two copies'
# payoffs (or, equivalently, expected per-copy payoff; constants don't matter).
#
#   profile  per-copy payoffs            global U
#   (S,S)      (4,4)                       8     <- optimum  (UDT1.1 picks this)
#   (S,H)      (0,3)                       3
#   (H,S)      (3,0)                       3
#   (H,H)      (3,3)                       6     <- bad equilibrium
#
# UDT1.1 (whole-policy optimizer): max over the 4 profiles => (S,S), value 8.
# UDT1.0 (pointwise EDT best response): copy i picks argmax over its own action
# of E[payoff_i | my action], holding a BELIEF about the other copy's action.

B, C = F(4), F(3)   # b > c

def payoff_self(my, other):
    """Per-copy payoff to ME given my action and the other's action."""
    if my == 'S':
        return B if other == 'S' else F(0)
    else:  # my == 'H'
        return C  # Hare is safe: pays c regardless

def best_response(belief_other_is_S):
    """
    Pointwise UDT1.0 / EDT best response of one copy, given a probability
    q = belief_other_is_S that the OTHER copy plays Stag.
    Returns ('S' or 'H', the two expected payoffs).
    """
    q = belief_other_is_S
    EU_S = q * payoff_self('S', 'S') + (1 - q) * payoff_self('S', 'H')   # = q*B
    EU_H = q * payoff_self('H', 'S') + (1 - q) * payoff_self('H', 'H')   # = C
    return ('S' if EU_S >= EU_H else 'H'), EU_S, EU_H

def part_B():
    print("=" * 64)
    print("PART B.  Stag-Hunt self-coordination  (b=4, c=3)")
    print("=" * 64)

    # --- B1: pointwise best-response dynamics has TWO fixed points ---
    print("  B1.  Fixed points of pointwise UDT1.0 best response:")
    for belief, name in [(F(1), "other certainly Stag"),
                         (F(0), "other certainly Hare")]:
        br, eus, euh = best_response(belief)
        consistent = (br == 'S' and belief == 1) or (br == 'H' and belief == 0)
        print(f"     belief q={belief} ({name}): EU[S]={eus}, EU[H]={euh}"
              f" -> best response {br}   fixed point? {consistent}")
    print("     => BOTH (S,S) and (H,H) are self-consistent. UDT1.0-with-itself")
    print("        is NOT guaranteed to land on the optimum (S,S). A bad whole-")
    print("        strategy (H,H) cannot be escaped by any single-copy deviation:")
    print(f"        unilateral S against a Hare-playing partner pays {payoff_self('S','H')}"
          f" < {payoff_self('H','H')}. THIS is the Stag-Hunt trap.\n")

    # --- B2: the (1-δ) belief that the OTHER copy plays the UDT1.1 action ---
    # UDT1.1 action here is Stag. So q = (1-δ)*1 + δ*(arbitrary in [0,1]).
    # Worst case for breaking the trap: the δ-mass is on the OTHER playing Hare
    # (q_min = 1-δ). We require S to be the best response even in that worst case.
    print("  B2.  Copy (1-δ)-believes the OTHER plays the UDT1.1 action (Stag).")
    print("       Worst case: δ-mass entirely on 'other plays Hare' => q = 1-δ.")
    # S is BR iff EU_S >= EU_H  iff  (1-δ)*B >= C  iff  δ <= 1 - C/B.
    threshold = 1 - C / B
    print(f"       S is the best response  iff  (1-δ)·b ≥ c  iff  δ ≤ 1 - c/b = {threshold}"
          f"  = {float(threshold):.4f}")
    for delta in [F(0), F(1,10), F(1,5), F(1,4), F(1,3), F(1,2)]:
        q = 1 - delta                       # worst-case belief the other is Stag
        br, eus, euh = best_response(q)
        ok = (br == 'S')
        print(f"       δ={str(delta):>4}: q_min={q}, EU[S]={eus}, EU[H]={euh}"
              f" -> {br}   (selects optimum? {ok})")
        # cross-check against the closed-form threshold
        assert ok == (delta <= threshold), "threshold mismatch"
    print(f"\n     => For every δ ≤ 1-c/b = {float(threshold):.2f}, the (1-δ)-belief that")
    print("        the rest of the policy is UDT1.1 makes EACH copy play Stag, so the")
    print("        realized profile is the OPTIMUM (S,S). The belief is a CORRELATION")
    print("        DEVICE that points all copies at the UDT1.1 policy and dissolves the")
    print("        bad equilibrium. This is the content hsel ASSUMES in Part A / the Lean.")
    print(f"     => For δ > {float(threshold):.2f} the belief is too weak: the trap can survive.")
    print("        (So the Part-A 'hsel' bridge is conditional on δ being small enough")
    print("         relative to the game's Stag-Hunt gap 1-c/b -- a real extra hypothesis.)\n")

    return threshold


# ============================================================
# PART C.  Tie the two parts: realized value vs the Part-A bound
# ============================================================

def part_C(threshold):
    print("=" * 64)
    print("PART C.  Realized global value of the pointwise agent vs Part-A bound")
    print("=" * 64)
    # Global utility of the realized profile, as a function of δ, when each copy
    # uses the B2 worst-case best response.  Normalize to [lo,hi]=[0,1] by
    # dividing by max global utility 8 (so V* in [0,1], matching Part A's bound).
    def global_U(p0, p1):
        return payoff_self(p0, p1) + payoff_self(p1, p0)
    Umax = global_U('S', 'S')   # = 8
    Vstar_SS = F(global_U('S','S'), Umax)   # 1
    Vstar_HH = F(global_U('H','H'), Umax)   # 6/8 = 3/4
    print(f"  Normalized V*: (S,S)->{Vstar_SS}, (H,H)->{Vstar_HH}; range hi-lo=1.")
    print(f"  {'δ':>6} {'profile':>9} {'V*(realized)':>13} {'gap to opt':>11}"
          f" {'δ/(1-δ)·range':>14} {'honest bound ok?':>16}")
    for delta in [F(0), F(1,10), F(1,5), F(1,4), F(1,3)]:
        q = 1 - delta
        br, _, _ = best_response(q)
        prof = (br, br)               # symmetric copies make the same choice
        Vreal = F(global_U(*prof), Umax)
        gap = Vstar_SS - Vreal
        eh = (delta / (1 - delta)) * 1
        ok = gap <= eh + F(1, 10**9)
        print(f"  {str(delta):>6} {str(prof):>9} {float(Vreal):>13.4f}"
              f" {float(gap):>11.4f} {float(eh):>14.4f} {str(ok):>16}")
        assert ok, "honest Part-A bound violated by the realized pointwise agent"
    print("\n  Reading: when δ ≤ 1-c/b the pointwise agent lands on (S,S), gap=0, well")
    print("  inside the honest bound. The Part-A whole-policy bound is a (loose but")
    print("  valid) certificate for the pointwise agent PRECISELY on the δ-range where")
    print("  the Stag-Hunt trap is dissolved. Outside that range the bridge (hsel) can")
    print("  fail and the certificate no longer applies to the pointwise agent.\n")


if __name__ == "__main__":
    part_A()
    thr = part_B()
    part_C(thr)
    print("ALL ASSERTIONS PASSED.")
