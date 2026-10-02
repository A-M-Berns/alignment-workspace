"""S2 / Statement 13: the base-rate identity along a trajectory, and class aggregation.

(1) Exact equivalence  rho >= q  <=>  alpha/beta <= eps/(1-eps) * h/c , on random draws
    (re-check of run-1 li I13.1, here with all parameters varying along a trajectory).
(2) Aggregation counterexample: two press classes; the overall (mixture) base-rate inequality
    holds, yet one efficiently detectable class violates it. Hence 'the false-press rate keeps
    pace' must be read class-wise relative to the agent's weighting class, not on the mixture.
"""
import random
random.seed(11)
def rho(eps, a, b): return eps*b/(eps*b + (1-eps)*a)
bad = 0
for n in range(1, 50001):
    c, h = random.uniform(0.1, 5), random.uniform(0.1, 50); q = c/(c+h)
    eps = 0.5/(1 + n/500) * random.uniform(0.2, 1.0)
    a, b = random.uniform(0.001, 0.9), random.uniform(0.1, 1.0)
    lhs = rho(eps, a, b) >= q
    rhs = a/b <= eps/(1-eps) * h/c
    bad += (lhs != rhs)
print(f"(1) mismatches between rho>=q and alpha/beta <= eps/(1-eps)*h/c over 50000 draws: {bad}")
# (2) two classes; class 0 (weight w0 of days) informative, class 1 (weight w1) noisy; same eps
c, h = 1.0, 20.0; q = c/(c+h); eps = 0.01; b = 0.9
a0 = 0.01
p0 = eps*b + (1-eps)*a0; r0 = rho(eps, a0, b)
print(f"(2) q={q:.4f}, eps={eps}, beta={b}; critical alpha/beta = eps/(1-eps)*h/c = {eps/(1-eps)*h/c:.4f}")
for w1, a1 in ((0.05, 0.6), (0.05, 0.25), (0.20, 0.6), (0.50, 0.6)):
    w0 = 1 - w1
    p1 = eps*b + (1-eps)*a1; r1 = rho(eps, a1, b)
    rmix = (w0*p0*r0 + w1*p1*r1)/(w0*p0 + w1*p1)   # mixture over pressed days
    print(f"    class1 share of days={w1:.2f}, alpha1={a1}: class0 rho={r0:.4f} ({'>=' if r0>=q else '<'} q); "
          f"class1 rho={r1:.4f} ({'>=' if r1>=q else '<'} q); mixture rho={rmix:.4f} ({'>=' if rmix>=q else '<'} q)")
print("    reading: with class1 a small share of days, the MIXTURE clears q while class1 is mostly false;")
print("    a coarse (class-blind) calibrated agent complies on all presses, a class-aware one defies class1.")
