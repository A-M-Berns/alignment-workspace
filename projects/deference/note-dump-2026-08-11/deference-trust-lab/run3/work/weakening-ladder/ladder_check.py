"""
run3 / weakening-ladder : exact-rational verification of every witness used in
WeakeningLadder.lean, using fractions.Fraction only (no floats anywhere).

The four rungs of faithful-acceleration.md §5 (line 124-134), in the document's
own soft gates  Ind_delta(x > c) = softInd(delta, x - c),  softInd(d,x) = clamp(x/d, 0, 1):

  bounded-violation : sum_n g_n * softInd(d, t - p_n)        < inf
  limit             : g_n * (p_n - t)  ->=~ 0   (liminf >= 0)
  bounded-eps-viol  : sum_n w_n < inf,  w_n = g_n * softInd(d, t - eps - p_n)
  averaged          : (sum g_n p_n)/(sum g_n)  >=~  t - eps - delta

Checks below (all asserts; the script FAILS LOUDLY if any number is off):
  [B]  the middle-rung counterexample (limit holds, sum w = inf, averaged fails)
  [E1] creep witness: limit holds, margin-free bounded-violation fails
  [E2] park witness:  bounded-eps-violation holds (sum w = 0), limit fails
  [E3] gap witness:   averaged holds at 9/16 >= 1/2, but w_n = 1/2 so sum w = inf
  [E4] alternating witness: bare gated mean >= t for all N>=1, yet w_n = 1 on odd days
  [C]  the repair's contrapositive arithmetic on the creep witness (w_n = 0 eventually)
"""

from fractions import Fraction as F

def softInd(d, x):
    """max 0 (min 1 (x/d)) -- the corpus clamp ramp, FaithfulAcceleration.lean:152."""
    return max(F(0), min(F(1), x / d))

def gate(d, t, a):
    return softInd(d, a - t)

LOG = []
def report(s):
    print(s)
    LOG.append(s)

# ---------------------------------------------------------------- [B] the counterexample
t, eps, d = F(3, 4), F(1, 8), F(1, 8)
report("[B] middle-rung counterexample: t=3/4, eps=delta=1/8, a_n = t + delta/(n+1), p == 0")
N = 4000
gsum = F(0); wsum = F(0); qmin_tail = None
for n in range(N):
    a_n = t + d / (n + 1)
    g_n = gate(d, t, a_n)
    assert g_n == F(1, n + 1), (n, g_n)                    # gate is exactly harmonic
    p_n = F(0)
    w_n = g_n * softInd(d, t - eps - p_n)
    assert softInd(d, t - eps - p_n) == 1                  # inner ramp saturates (5/8 >= 1/8)
    assert w_n == F(1, n + 1)
    q_n = g_n * (p_n - t)
    assert q_n == -t / (n + 1)                             # -> 0, so the limit rung HOLDS
    gsum += g_n; wsum += w_n
# partial sums of w grow like log N -- exceed 8 by N=4000 (H_4000 ~ 8.9)
assert wsum > 8, wsum
report(f"    q_n = -(3/4)/(n+1) -> 0  (limit rung holds);  sum_{{n<{N}}} w_n = {wsum} > 8 (diverges)")
# averaged rung: numerator identically 0, so gated average = 0 < t-eps-delta = 1/2
report(f"    gated average = 0 < t-eps-delta = {t-eps-d}  (averaged rung FAILS too)")
assert t - eps - d == F(1, 2)
# gate has no support gap: g_n = 1/(n+1) takes values below any c>0 while positive
report("    gate support-degenerate: g_n = 1/(n+1) > 0 but inf = 0  (repair hypothesis violated)")

# ---------------------------------------------------------------- [E1] creep witness
report("[E1] creep: a == 7/8 (gate == 1), p_n = 3/4 - 1/(n+1), t=3/4, delta=1/8")
vsum = F(0)
for n in range(N):
    g_n = gate(d, t, F(7, 8))
    assert g_n == 1
    p_n = t - F(1, n + 1)
    v_n = g_n * softInd(d, t - p_n)                        # margin-FREE violation weight
    assert v_n >= F(1, n + 1)                              # >= harmonic => diverges
    q_n = g_n * (p_n - t)
    assert q_n == -F(1, n + 1)                             # -> 0: limit rung HOLDS
    vsum += v_n
assert vsum > 8, vsum
report(f"    limit holds (q_n = -1/(n+1));  margin-free sum_{{n<{N}}} v_n = {vsum} > 8 (bounded-violation FAILS)")

# [C] repair on the same creep witness: with margin eps=1/8, w_n = softInd(d, 1/(n+1) - 1/8) = 0 once n>=8
for n in range(N):
    p_n = t - F(1, n + 1)
    w_n = softInd(d, t - eps - p_n)
    if n >= 8:
        assert w_n == 0, (n, w_n)
report("[C]  repair fires on creep (hard gate, c=1): w_n = 0 for all n >= 8, so sum w < inf")

# ---------------------------------------------------------------- [E2] park witness
report("[E2] park: p == t - eps/2 = 11/16, gate == 1")
p_park = t - eps / 2
assert p_park == F(11, 16)
assert softInd(d, t - eps - p_park) == 0                   # arg = -eps/2 < 0
report(f"    w_n == 0 (sum w = 0 < inf: bounded-eps-violation HOLDS); q_n == {p_park - t} < 0 forever (limit FAILS)")
assert p_park - t == -F(1, 16)
# bare gated mean = 11/16 < t: the (ii) half of the no-cancellation incomparability pair
assert p_park < t
report(f"    bare gated mean = {p_park} < t = {t}  (Theorem holds, mean-form fails: incomparability half (ii))")

# ---------------------------------------------------------------- [E3] gap witness
report("[E3] gap: p == t - eps - delta/2 = 9/16, gate == 1")
p_gap = t - eps - d / 2
assert p_gap == F(9, 16)
w_gap = softInd(d, t - eps - p_gap)
assert w_gap == F(1, 2)                                    # ramp value (1/16)/(1/8)
assert p_gap >= t - eps - d                                # 9/16 >= 1/2: averaged rung HOLDS
report(f"    averaged holds ({p_gap} >= {t-eps-d}) but w_n == {w_gap}, sum w = inf: the delta-gap, Corollary strictly weaker than Theorem")

# ---------------------------------------------------------------- [E4] alternating witness
t2 = F(2, 5)
report("[E4] alternating: t=2/5, gate == 1 (a == 21/40), p_n = 1 on even n, 0 on odd n")
S = F(0)
for Nn in range(1, 401):
    n = Nn - 1
    p_n = F(1) if n % 2 == 0 else F(0)
    if p_n == 0:
        w_n = softInd(d, t2 - eps - p_n)
        assert w_n == 1                                    # 2/5-1/8 = 11/40 >= 1/8: saturates
    S += p_n
    assert S / Nn >= t2, (Nn, S)                           # bare gated mean >= t for every N>=1
report("    bare gated mean >= 2/5 for all 1<=N<=400, yet w_n = 1 on every odd day (sum w = inf):")
report("    incomparability half (i): mean-form holds, Theorem fails -- no mean inequality encodes sum w < inf")

report("ALL EXACT-RATIONAL CHECKS PASSED")

with open(__file__.replace("ladder_check.py", "ladder_check.out.txt"), "w") as f:
    f.write("\n".join(LOG) + "\n")
