"""
trace_nonrec.py -- exact-rational check of the trace-nonrecoverability construction
(run3 TODO `trace-nonrecoverability`; finite shadow of v6 section 4.7 ingredient (d)).

Everything is fractions.Fraction; no floats anywhere. Every claim is an assert.

Rule class: a system S = (h, beta, a) over horizon T = 4, where
  h[n]    = latent autonomous verdict stream (what the human's own deliberation
            delivers on day n, absent any influence),
  beta[n] = latent influence map, in [0,1] (weight with which the human adopts
            the advisor's quote on day n),
  a[n]    = published quote stream.
Run semantics (the human's realized day-n opinion on the designated
never-decided target, which it also publishes as feedback):
  Y[n] = (1 - beta[n]) * h[n] + beta[n] * a[n]
Observable trace: [(a[n], Y[n]) for n < T].
A-free counterfactual: run the SAME system with the influence map zeroed
(the influence map is the only A->H channel), i.e. Y0[n] = h[n].
Legitimacy defect: d(S) = |Y[T-1] - Y0[T-1]|.
"""

from fractions import Fraction as F

T = 4


def run(h, beta, a):
    """The run: realized opinion/feedback stream."""
    return [(1 - beta[n]) * h[n] + beta[n] * a[n] for n in range(T)]


def trace(h, beta, a):
    """Observable record: all published quotes + all realized feedback."""
    Y = run(h, beta, a)
    return [(a[n], Y[n]) for n in range(T)]


def afree(h, beta, a):
    """The A-free system: influence map zeroed. Same rule class member shape."""
    return (h, [F(0)] * T, a)


def defect(h, beta, a):
    """|terminal opinion - A-free counterfactual terminal opinion|,
    with the counterfactual computed by actually running the A-free system."""
    Y = run(h, beta, a)
    Y0 = run(*afree(h, beta, a))
    return abs(Y[T - 1] - Y0[T - 1])


def valid(h, beta, a):
    return all(0 <= x <= 1 for s in (h, beta, a) for x in s)


# ---- the two systems, same declared rule class, different latent parameters ----
h_faith = [F(1, 2), F(5, 8), F(3, 4), F(3, 4)]   # uninfluenced human deliberates to 3/4
h_steer = [F(1, 2), F(3, 8), F(1, 4), F(1, 4)]   # steered human would have gone to 1/4
quote = [F(1, 2), F(5, 8), F(3, 4), F(3, 4)]     # A's published quotes (same in both)

S1 = (h_faith, [F(0)] * T, quote)   # faithful: beta = 0, A tracks the human
S2 = (h_steer, [F(1)] * T, quote)   # steered: beta = 1, human adopts A's quotes

# ---- membership: both genuine members of the declared class ----
assert valid(*S1), "S1 not in class"
assert valid(*S2), "S2 not in class"
# latent parameters genuinely differ (non-degeneracy)
assert h_faith != h_steer and S1[1] != S2[1]

# ---- (i) trace equality: computed, not asserted ----
tr1, tr2 = trace(*S1), trace(*S2)
assert tr1 == tr2, "trace equality FAILS"
print("trace S1 == trace S2 :", tr1)

# perfect apparent tracking in BOTH systems (the whispering-earring surface)
assert all(an == yn for (an, yn) in tr1)
assert all(an == yn for (an, yn) in tr2)
print("perfect apparent tracking (a_n == Y_n) holds in both runs")

# ---- (ii)+(iii) counterfactual baselines by running the A-free systems ----
Y0_1 = run(*afree(*S1))
Y0_2 = run(*afree(*S2))
print("A-free run of S1:", Y0_1)
print("A-free run of S2:", Y0_2)
d1, d2 = defect(*S1), defect(*S2)
assert d1 == F(0)
assert d2 == F(1, 2)
gamma = d2
print(f"defect d(S1) = {d1},  d(S2) = {d2}  (gamma = {gamma} > 0)")

# ---- (iv) impossibility: every function of the trace agrees on S1, S2.
# Finitely witnessed here by extensionality: tr1 == tr2, so l(tr1) == l(tr2)
# for ANY l; in particular no l with l(tr1) = d(S1) and l(tr2) = d(S2) exists,
# since that would force d(S1) == d(S2), refuted:
assert d1 != d2
print("no function of the trace can equal the defect on {S1, S2}:",
      "tr1 == tr2 but d1 != d2")

# ---- (v) transparency near-miss: reveal the influence map; a separator exists ----
def trace_plus(h, beta, a):
    return (tuple(trace(h, beta, a)), tuple(beta))

def sep(tplus):
    """gate on the ENLARGED record: 'did any influence occur?'"""
    return tplus[1] != (F(0),) * T

tp1, tp2 = trace_plus(*S1), trace_plus(*S2)
assert sep(tp1) is False and sep(tp2) is True
assert sep(tp1) == (d1 > 0) and sep(tp2) == (d2 > 0)
print("transparency near-miss: sep(trace+ S1) =", sep(tp1),
      ", sep(trace+ S2) =", sep(tp2), " -- matches the legitimacy predicate d>0")

# ---- (vi) corruption deletion test: zero S2's influence map; trace equality FAILS ----
S2_deleted = afree(*S2)
assert trace(*S2_deleted) != tr1, "deletion test FAILS: influence map inert"
assert defect(*S2_deleted) == 0
print("deletion test: trace(S2 with beta:=0) =", trace(*S2_deleted))
print("               differs from the shared trace at day 1:",
      trace(*S2_deleted)[1], "vs", tr1[1])

# ---- general lemma check (kernel-checked in Lean as
#      hidden_defect_needs_full_influence): within the class, perfect apparent
#      tracking at the terminal day forces beta[T-1] = 1 or defect 0.
# Exhaustive sweep over a rational grid.
grid = [F(k, 8) for k in range(9)]
count_hidden = 0
for hh in grid:
    for bb in grid:
        for aa in grid:
            h = [hh] * T; beta = [bb] * T; a = [aa] * T
            Y = run(h, beta, a)
            if a[T - 1] == Y[T - 1]:                # perfect tracking at terminal day
                d = defect(h, beta, a)
                assert bb == 1 or d == 0, (hh, bb, aa)
                if d > 0:
                    count_hidden += 1
                    assert bb == 1
print(f"sweep 9^3 = {9**3} constant-parameter systems: every hidden defect "
      f"under a perfect-tracking trace has beta = 1 ({count_hidden} such systems)")

print("ALL ASSERTS PASSED")
