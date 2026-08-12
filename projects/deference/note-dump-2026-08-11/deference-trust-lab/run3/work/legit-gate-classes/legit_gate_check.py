"""
run3 TODO 1 -- legit-gate-classes: exact-rational sanity check (illustration, not evidence;
the evidence is the kernel-checked LegitGateClasses.lean).

Verifies, with fractions.Fraction (no floats), the finite behavior of every compiled
witness in LegitGateClasses.lean:

  T2+  ungated calibration:   w=1, bias (-1)^n       -> |ratio(n)| <= 1/n
  T2-  gated breakage:        gate cEven (error-correlated) -> ratio(n) == 1 for n>=1
  T2d  deletion test:         gate c=1 recovers the ungated ratio exactly
  T1w  weaker antecedent:     bias bOdd: ungated ratio(2m) == 1/2 (fails ->0);
                              gated by cEven: ratio == 0 identically (holds)
  T3   closure instance:      gate cMix (non-constant, interior-valued, in PairClass)
                              on w=1 against (-1)^n: |ratio(n)| <= 1/den(n), den -> inf
  SIL  silence:               gate c_n = 1/2^n (bounded mass): gated violation mass
                              bounded by 2 for ALL n, for the maximally-violating w=1
"""

from fractions import Fraction as F

N = 2001  # horizon

def ratio(num, den):
    return F(0) if den == 0 else F(num, 1) / den

# --- sequences (mirror the Lean definitions exactly) ---
bAlt  = lambda n: F(-1) ** n                    # (-1)^n
bOdd  = lambda n: F(1) if n % 2 == 1 else F(0)
wOne  = lambda n: F(1)
cEven = lambda n: F(1) if n % 2 == 0 else F(0)
cOne  = lambda n: F(1)
cMix  = lambda n: F(1) if n % 4 <= 1 else F(1, 2)

def partials(c, w, b, N):
    """returns lists den[n] = sum_{i<n} c_i w_i, num[n] = sum_{i<n} c_i w_i b_i"""
    den, num = [F(0)], [F(0)]
    for i in range(N - 1):
        den.append(den[-1] + c(i) * w(i))
        num.append(num[-1] + c(i) * w(i) * b(i))
    return den, num

# T2+ : ungated calibration (w=1, bias (-1)^n): |ratio| <= 1/n
den, num = partials(cOne, wOne, bAlt, N)
for n in range(1, N):
    r = ratio(num[n], den[n])
    assert abs(r) <= F(1, n), (n, r)
    assert num[n] == (0 if n % 2 == 0 else 1)          # exact pairwise cancellation
print("T2+  ungated calibration      : |ratio(n)| <= 1/n for all n < %d   OK" % N)

# T2- : gated by the error-correlated cEven: ratio == 1 identically (n>=1)
den, num = partials(cEven, wOne, bAlt, N)
for n in range(1, N):
    assert ratio(num[n], den[n]) == 1, n
    assert den[n] == (n + 1) // 2                       # infinite gated mass (non-silent)
print("T2-  gated breakage (cEven)   : ratio(n) == 1 for 1 <= n < %d      OK" % N)

# T2d : deletion test: gate c=1 gives literally the ungated ratio
denu, numu = partials(cOne, wOne, bAlt, N)
dend, numd = partials(lambda n: F(1), wOne, bAlt, N)
assert denu == dend and numu == numd
print("T2d  deletion test (c == 1)   : gated ratio == ungated ratio exactly OK")

# T1w : weaker antecedent, bias on odd days
den, num = partials(cOne, wOne, bOdd, N)
for m in range(1, N // 2):
    assert ratio(num[2 * m], den[2 * m]) == F(1, 2), m  # ungated fails: stuck at 1/2
den, num = partials(cEven, wOne, bOdd, N)
for n in range(N):
    assert num[n] == 0                                  # gated holds: ratio identically 0
print("T1w  weaker antecedent        : ungated ratio(2m) == 1/2; gated == 0  OK")

# T3 : closure instance, non-constant interior gate cMix in PairClass
assert cMix(0) == 1 and cMix(2) == F(1, 2)              # non-constant (compiled too)
for m in range(N // 2):                                  # pair-equality (class membership)
    assert cMix(2 * m + 1) == cMix(2 * m)
assert not (cEven(1) == cEven(0))                        # cEven is NOT in PairClass
den, num = partials(cMix, wOne, bAlt, N)
for n in range(1, N):
    assert abs(num[n]) <= 1                              # single-term numerator bound
    if den[n] > 0:
        assert abs(ratio(num[n], den[n])) <= F(1, 1) / den[n]
assert den[N - 1] >= F(N - 1, 2) * F(1, 2)               # divergent gated mass
print("T3   closure instance (cMix)  : |ratio(n)| <= 1/den(n), den -> inf   OK")

# SIL : silence — summable gate, maximally-violating weight, mass stays bounded
csum, mass = F(0), F(0)
for i in range(N):
    csum += F(1, 2 ** i)
    mass += F(1, 2 ** i) * wOne(i)
    assert mass <= 2
print("SIL  silence (c_n = 2^-n)     : gated violation mass <= 2 for all n  OK")

print("\nall exact-rational checks passed (horizon N = %d)" % N)
