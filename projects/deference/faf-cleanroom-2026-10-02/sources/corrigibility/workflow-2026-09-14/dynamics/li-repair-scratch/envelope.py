"""Envelope of the Statement-5 family k1 <= r(f,p) k0 + K_f over f, with the wealth cap C held FIXED
(the counterfactual in which the criterion's constant were uniform in the trader).  Shows the envelope is
p/(1-p) k0 + O(sqrt(k0)) -- the LIL shape of Statement 1(c) -- and that with C fixed the excess over the odds
line grows like sqrt(k0), never a constant.  Also: for fixed f, the family's inequality is implied eventually by
ratio-unbiasedness (k1/k0 -> p/(1-p) from below), checked on a synthetic record."""
import math
p = 0.05
odds = p/(1-p)
def r(f): return math.log(1/(1-f))/math.log(1+f*(1/p-1))
def K(f, C): return math.log(C)/math.log(1+f*(1/p-1))
print("p=%.3f odds=%.4f" % (p, odds))
for C in (2.0, 10.0):
    print("C=%g" % C)
    for k0 in (10, 100, 1000, 10000, 100000):
        fs = [10**(-e/20) for e in range(1, 121)]  # f from ~0.89 down to 1e-6
        best = min((r(f)*k0 + K(f, C), f) for f in fs)
        excess = best[0] - odds*k0
        print("  k0=%7d  envelope=%12.3f  odds*k0=%12.3f  excess=%9.3f  excess/sqrt(k0)=%.3f  argmin f=%.2e"
              % (k0, best[0], odds*k0, excess, excess/math.sqrt(k0), best[1]))
# fixed-f inequality is eventually implied by ratio convergence: k1(N) = floor(odds*k0(N)*(1 - 1/sqrt(k0)))
print("fixed f=0.1: r=%.4f; check k1 <= r k0 + K for synthetic record with k1/k0 -> odds from below" % r(0.1))
viol = 0
for k0 in range(1, 200001):
    k1 = math.floor(odds*k0*(1 - 1/math.sqrt(k0))) if k0 > 1 else 0
    if k1 > r(0.1)*k0 + K(0.1, 2.0): viol += 1
print("  violations over k0 <= 2e5:", viol)
