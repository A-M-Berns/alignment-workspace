#!/usr/bin/env python3
"""
Fast-Student / Slow-Teacher merge: numerical micro-example.

Two "inductors" H (slow, trusted) and A (fast, untrusted) over a shared theory Gamma.
We do NOT build real logical inductors (infeasible). Instead we model their PRICE
SEQUENCES directly as number sequences chosen to satisfy the relevant LI ASYMPTOTIC
identities, and check that the derived merge

    B_t(phi) := E^A_t( <P^H_{f(t)}(phi)> )      ("A's day-t estimate of H's day-f(t) price")

satisfies (a) inductor-ness on the good-feedback subsequence (it tracks H's limit), and
(b) the cross-agent martingale that drives H's endorsement of B (v2 section 10 Value).

We then EXHIBIT the failure off the good-feedback subsequence (idea-1b "no-feedback hole").

Everything here is checked numerically against the definitions; the script PRINTS PASS/FAIL.
This is a model verification, NOT a proof. The proof status is SKETCHED (see the .md).
"""

import math
import random

random.seed(0)

# ---------------------------------------------------------------------------
# Setup: a 2-option menu and a single tracked sentence, over many "days".
# We use a deferral function f(t) = 2t (strictly increasing, f(t)>t). The
# "fast enough f" hypothesis is encoded by: H's day-f(t) price is decided
# (computable) by day t+1 of A's clock on the good-feedback subsequence.
# ---------------------------------------------------------------------------

N = 4000                      # number of days
def f(t): return 2 * t        # deferral function (strictly increasing)

# H is a logical inductor whose price on phi CONVERGES to a limit p_inf.
# We give H a converging-but-noisy price path: P^H_n(phi) -> p_inf.
p_inf = 0.7
def PH(n):
    """H's day-n market price of phi. Converges to p_inf at rate ~1/n with
    bounded oscillation (an LI-plausible price path)."""
    if n < 1:
        return 0.5
    return p_inf + (0.4 * math.sin(n) ) / (1 + 0.5 * n)

# A's market produces, on day t, an ESTIMATE of the number P^H_{f(t)}(phi).
# This is B_t(phi). On the GOOD-FEEDBACK subsequence, A is unbiased for the
# realized value P^H_{f(t)}(phi): the (w-weighted) average of (B_t - P^H_{f(t)})
# tends to 0. We model A as: realized H-value plus a mean-zero (w-weighted) noise.
def Bgood(t):
    """B_t(phi) on a day t that is IN the good-feedback subsequence.
    A is unbiased: estimate = realized P^H_{f(t)}(phi) + zero-mean shrinking noise."""
    truth = PH(f(t))
    noise = 0.3 * math.cos(3 * t) / (1 + 0.2 * t)   # oscillating, w-mean ~ 0
    return min(1.0, max(0.0, truth + noise))

def Bbad(t):
    """B_t(phi) OFF the good-feedback subsequence (the 'unobservable class'):
    no poly-time machine decides P^H_{f(t)}(phi) before A must price it, so the
    good-feedback hypothesis is VACUOUS. A's estimate can be anything; we model
    a persistent BIAS b that w-averaging does NOT kill."""
    truth = PH(f(t))
    persistent_bias = -0.25                          # A systematically lowballs H here
    return min(1.0, max(0.0, truth + persistent_bias))

# ---------------------------------------------------------------------------
# (a) B inherits inductor-ness ON the good-feedback subsequence:
#     the w-weighted average of B_t(phi) tracks H's limit p_inf.
# We use a P^H-generable divergent weighting w_t = 1 (uniform) on the subsequence.
# ---------------------------------------------------------------------------
def weighted_avg(vals, w):
    num = sum(v * wi for v, wi in zip(vals, w))
    den = sum(w)
    return num / den if den else float('nan')

days = list(range(1, N))
w = [1.0] * len(days)         # uniform divergent weighting (P^H-generable trivially)

B_good_vals = [Bgood(t) for t in days]
B_bad_vals  = [Bbad(t)  for t in days]
PH_fut      = [PH(f(t)) for t in days]   # realized H future prices

# Tail averages (asymptotic ~_t means difference -> 0; we look at the last 25% of days).
tail = slice(int(0.75 * len(days)), None)

avg_Bgood_tail = weighted_avg(B_good_vals[tail], w[tail])
avg_Bbad_tail  = weighted_avg(B_bad_vals[tail],  w[tail])
avg_PHfut_tail = weighted_avg(PH_fut[tail],      w[tail])

print("=== (a) B tracks H's limit on the good-feedback subsequence ===")
print(f"  p_inf (H's limit)                         = {p_inf:.4f}")
print(f"  tail w-avg of realized P^H_f(t)(phi)      = {avg_PHfut_tail:.4f}")
print(f"  tail w-avg of B_t (good feedback)         = {avg_Bgood_tail:.4f}")
print(f"  tail w-avg of B_t (NO feedback / biased)  = {avg_Bbad_tail:.4f}")
ok_a_good = abs(avg_Bgood_tail - p_inf) < 0.02
ok_a_bad  = abs(avg_Bbad_tail  - p_inf) > 0.10   # bad case demonstrably NOT tracking
print(f"  [good-feedback B tracks p_inf to <0.02] : {'PASS' if ok_a_good else 'FAIL'}")
print(f"  [no-feedback  B FAILS to track (>0.10)] : {'PASS' if ok_a_bad else 'FAIL'}")
print()

# ---------------------------------------------------------------------------
# (b) Cross-agent martingale / H's endorsement of B (v2 section 10 Value).
#
# We instantiate v2 section 3 / section 10 with a 2-option menu O^1, O^2 whose
# day-f(t) H-VALUES are functions of P^H_{f(t)}(phi):
#     O^1_t value = P^H_{f(t)}(phi)            (bet "phi is true")
#     O^2_t value = 1 - P^H_{f(t)}(phi)        (bet "phi is false")
# The expert estimate fed to the softmax selector is B_t (= A's read of H's future):
#     m^1_t = B_t(phi),     m^2_t = 1 - B_t(phi)
# Selection weights: alpha^j_t = softmax(m^j / delta_t),  delta_t -> 0.
# Strategy return  Shat_t = sum_j alpha^j_t * O^j_t  (paid out at H's day-f(t) values).
#
# Value (LI form):  E^H_t( Shat_t )  >~_t  E^H_t( O^i_t )  for each fixed i.
# We approximate E^H_t(X) of these LUVs by the realized H-day-f(t) value (the merge's
# 'good feedback' makes B ~ realized, and H's own martingale makes E^H_t(X) ~ realized
# on the subsequence). So the numerical surrogate for Value is:
#     avg_t [ Shat_t ]  >~  avg_t [ O^i_t ]    on the tail, weighted by w.
# ---------------------------------------------------------------------------
def softmax2(m1, m2, delta):
    a = math.exp(m1 / delta)
    b = math.exp(m2 / delta)
    Z = a + b
    return a / Z, b / Z

def value_check(Bfun, label):
    Shat = []
    O1   = []
    O2   = []
    for k, t in enumerate(days):
        delta = 1.0 / math.sqrt(t + 1)          # temperature -> 0
        b = Bfun(t)
        m1, m2 = b, 1 - b                        # expert (B) estimates of the two bets
        a1, a2 = softmax2(m1, m2, delta)
        v1 = PH(f(t))                            # realized H day-f(t) value of O^1
        v2 = 1 - PH(f(t))                        # realized H day-f(t) value of O^2
        Shat.append(a1 * v1 + a2 * v2)
        O1.append(v1)
        O2.append(v2)
    avg_S  = weighted_avg(Shat[tail], w[tail])
    avg_O1 = weighted_avg(O1[tail],   w[tail])
    avg_O2 = weighted_avg(O2[tail],   w[tail])
    print(f"=== (b) Value / endorsement check [{label}] ===")
    print(f"  tail w-avg E^H( Shat )  = {avg_S:.4f}")
    print(f"  tail w-avg E^H( O^1 )   = {avg_O1:.4f}")
    print(f"  tail w-avg E^H( O^2 )   = {avg_O2:.4f}")
    # Value: Shat >~ each option (up to a vanishing slack delta*log k).
    slack = 0.01
    ok1 = avg_S >= avg_O1 - slack
    ok2 = avg_S >= avg_O2 - slack
    print(f"  [Shat >~ O^1]: {'PASS' if ok1 else 'FAIL'}")
    print(f"  [Shat >~ O^2]: {'PASS' if ok2 else 'FAIL'}")
    print()
    return ok1 and ok2

ok_b_good = value_check(Bgood, "good feedback -> endorsement HOLDS")
ok_b_bad  = value_check(Bbad,  "no feedback -> endorsement may FAIL")

# ---------------------------------------------------------------------------
# Headline: the "one big lie" (idea 6) — a single high-stakes round can be
# arbitrarily wrong even when the AVERAGE endorsement holds. Demonstrate that a
# single t* with a big B-error does not violate the w-AVERAGE Value statement,
# i.e. endorsement is silent about the single round.
# ---------------------------------------------------------------------------
print("=== one-big-lie: average endorsement is silent about a single round ===")
tstar = days[int(0.8 * len(days))]
b_true = Bgood(tstar)
b_lie  = 0.0                      # treacherous: claim phi almost surely false at the key moment
print(f"  at t*={tstar}: honest B={b_true:.3f}, treacherous B={b_lie:.3f}, "
      f"single-round error={abs(b_true-b_lie):.3f}")
print("  (this one round can carry unbounded real-world stakes; the >~_t average")
print("   Value statement above does NOT bound it -- see idea 6 in the .md)")
print()

all_ok = ok_a_good and ok_a_bad and ok_b_good and (not ok_b_bad)
print("=== OVERALL ===")
print(f"  good-feedback endorsement holds, no-feedback endorsement fails as predicted: "
      f"{'PASS' if all_ok else 'CHECK'}")
