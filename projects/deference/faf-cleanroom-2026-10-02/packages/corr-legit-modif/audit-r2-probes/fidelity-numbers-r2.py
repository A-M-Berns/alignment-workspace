#!/usr/bin/env python3
"""corr-legit-modif audit round 2 (fidelity): independent exact recomputation of every numeral the
headlines carry, from the model of record as the sources state it (not from the Lean). Fractions
throughout. Each block prints the numbers and asserts the Lean's values. Run: python3 this file.
"""
from fractions import Fraction as F
from itertools import product

B = (True, False)

# ---------------------------------------------------------------- Y1 model of record (lgf Proofs l. 120)
eps = F(1, 10)
def pL(lam, l): return lam if l else 1 - lam
def pS(s): return eps if s else 1 - eps
def pSig(s, a, rates=(F(1, 10), F(9, 10))):      # (P(w|R), P(w|W))
    aR, aW = rates
    p = aW if s else aR
    return p if a else 1 - p
def pMod(l, s):
    return (F(9, 10) if s else F(1, 10)) if l else (F(1, 10) if s else F(9, 10))
def modRate(fake, l, s, a): return F(0) if (fake and not a) else pMod(l, s)
def joint(lam, fake, rates=(F(1, 10), F(9, 10))):
    P = {}
    for l, s, a, v in product(B, B, B, B):
        m = modRate(fake, l, s, a)
        P[(l, s, a, v)] = pL(lam, l) * pS(s) * pSig(s, a, rates) * (m if v else 1 - m)
    return P
X = lambda s: F(-4) if s else F(1)
def cont(numW, numR, ties_stop=True):
    return (4 * numW < numR) if ties_stop else (4 * numW <= numR)

qowW, qowR = eps * pMod(True, True), (1 - eps) * pMod(True, False)
def qadd(a): return eps * pMod(True, True) * pSig(True, a), (1 - eps) * pMod(True, False) * pSig(False, a)
def own(P, a): return sum(P[(l, True, a, False)] for l in B), sum(P[(l, False, a, False)] for l in B)
def value(lam, fake, additive, rates=(F(1, 10), F(9, 10)), ties_stop=True):
    P = joint(lam, fake, rates)
    V = F(0)
    for w, m in P.items():
        l, s, a, v = w
        if v:
            st = qadd(a) if additive else (qowW, qowR)
        else:
            st = own(P, a)
        if cont(*st, ties_stop=ties_stop):
            V += m * X(s)
    return V

tab = {(lam, fk, ad): value(lam, fk, ad) for lam in (F(1), F(9, 10)) for fk in B for ad in B}
print("Y1 table:", {k: str(v) for k, v in tab.items()})
assert tab[(F(1), False, False)] == F(77, 100) and tab[(F(1), True, False)] == F(163, 200)
assert tab[(F(1), False, True)] == F(163, 200) == tab[(F(1), True, True)]
assert tab[(F(9, 10), False, False)] == F(333, 500) and tab[(F(9, 10), True, False)] == F(779, 1000)
assert tab[(F(9, 10), False, True)] == F(779, 1000) == tab[(F(9, 10), True, True)]
assert tab[(F(1), True, False)] - tab[(F(1), False, False)] == F(9, 200) != F(1, 25)
assert tab[(F(9, 10), True, False)] - tab[(F(9, 10), False, False)] == F(113, 1000)
# same table under repair_checks.py's tie convention (>= 0): no tie occurs at Y1's numbers
for k, v in tab.items():
    assert value(k[0], k[1], k[2], ties_stop=False) == v

# ---------------------------------------------------------------- the scripts' successor frame and local trust
def frame_rows(lam):
    """rows as W-credence: install P(W | L, modify); keep rows P(W | keep, sigma_A) summed over l."""
    P = joint(lam, False)
    ZL = sum(P[w] for w in P if w[0] and w[3])
    inst = sum(P[w] for w in P if w[0] and w[3] and w[1]) / ZL
    rows = {}
    for w in P:
        if w[3]:
            rows[w] = inst
        else:
            nW, nR = own(P, w[2])
            rows[w] = nW / (nW + nR)
    return P, rows
def simple_trust_W_from_piL(lam):
    P, rows = frame_rows(lam)
    piL = {w: (P[w] if w[0] else F(0)) for w in P}
    thresholds = sorted(set(rows.values()))
    for t in thresholds:                       # above-threshold cuts: sum piL (1_W - t) over rows >= t
        above = sum(piL[w] * ((1 if w[1] else 0) - t) for w in P if rows[w] >= t)
        if above < 0:
            return False, (t, above)
        below = sum(piL[w] * ((1 if w[1] else 0) - t) for w in P if rows[w] <= t)
        if below > 0:
            return False, (t, below)
    return True, None
for lam, expect in ((F(1), True), (F(9, 10), True), (F(7, 10), True), (F(1, 2), False)):
    ok, why = simple_trust_W_from_piL(lam)
    print(f"local Simple Trust on W from pi_L at P(L)={lam}: {ok} {why}")
    assert ok == expect
P, rows = frame_rows(F(1, 2))
assert rows[(True, True, True, False)] == F(1, 2)      # keep-w row at 1/2: (9-8*1/2)/10 = 1/2
cutmass = sum(P[w] for w in P if w[0] and rows[w] >= F(1, 2))
cutW = sum(P[w] for w in P if w[0] and rows[w] >= F(1, 2) and w[1])
print("cut at t=1/2, P(L)=1/2: W-mass", cutW, "cut mass", cutmass)
assert cutW == F(99, 2000) and cutmass == F(270, 2000) and cutW < F(1, 2) * cutmass
for lam in (F(1), F(9, 10), F(7, 10), F(1, 2)):
    P, rows = frame_rows(lam)
    assert rows[(True, True, True, False)] == (9 - 8 * lam) / 10
    assert rows[(True, True, False, False)] == (9 - 8 * lam) / (90 + 640 * lam)
    # P(L | keep, sigma_A = w) = lam  (the own continuation is not L-certain)
    keepw = {w: P[w] for w in P if (not w[3]) and w[2]}
    assert sum(m for w, m in keepw.items() if w[0]) / sum(keepw.values()) == lam
print("row credences and P(L | keep, w) = lambda: ok")

# ---------------------------------------------------------------- reflection from the informed judge (P(L)=1)
P = joint(F(1), False)
for a, lhs in ((False, F(9, 1000)), (True, F(81, 1000))):
    joint_WM = sum(P[w] for w in P if w[0] and w[2] == a and w[3] and w[1])
    mod_mass = sum(P[w] for w in P if w[0] and w[2] == a and w[3])
    assert joint_WM == lhs and mod_mass * F(1, 2) == F(45, 1000) and joint_WM != mod_mass * F(1, 2)
qr, qw = qadd(False), qadd(True)
assert (qr[1] - 4 * qr[0]) / (qr[0] + qr[1]) == F(1, 2)
assert (qw[1] - 4 * qw[0]) / (qw[0] + qw[1]) == F(-7, 2)
assert (qowR - 4 * qowW) / (qowW + qowR) == F(-3, 2)
print("informed reflection failure 9/1000, 81/1000 vs 45/1000; expectations 1/2, -7/2, -3/2: ok")

# ---------------------------------------------------------------- T14: gain_eq and dodge_iff against brute force
def famValue(lam, a, b, fake):
    return value(lam, fake, False, rates=(a, b))
mism = 0; pts = 0; off_regime_dodges = 0
grid = [F(i, 10) for i in range(11)]
for lam in grid:
    for a in grid:
        for b in grid:
            pts += 1
            A = (9 * (1 - a) - 4 * (1 - b)) / 10
            K = (9 * (1 - a) * (1 + 8 * lam) - 4 * (1 - b) * (9 - 8 * lam)) / 100
            pred = (A if A > 0 else 0) - (K if K > 0 else 0)
            g = famValue(lam, a, b, True) - famValue(lam, a, b, False)
            if g != pred: mism += 1
            dodge = g > 0
            if dodge != (A > 0 and A - K > 0): mism += 1
            if dodge and not K > 0: off_regime_dodges += 1
print(f"T14 grid: {pts} points, mismatches {mism}, off-regime dodges {off_regime_dodges}")
assert mism == 0
assert famValue(F(0), F(0), F(1, 10), True) - famValue(F(0), F(0), F(1, 10), False) == F(27, 50)
for lam in grid:
    assert famValue(lam, F(1, 10), F(9, 10), True) - famValue(lam, F(1, 10), F(9, 10), False) == (725 - 680 * lam) / 1000

# ---------------------------------------------------------------- retention form (state mixture) and randomized install
def ret_value(r, fake, ties_stop=True):
    P = joint(F(1), fake)
    V = F(0)
    for w, m in P.items():
        l, s, a, v = w
        if v:
            qW, qR = qadd(a)
            nW = (1 - r) * qowW * (qW + qR) + r * qW * (qowW + qowR)
            nR = (1 - r) * qowR * (qW + qR) + r * qR * (qowW + qowR)
            st = (nW, nR)
        else:
            st = own(P, a)
        if cont(*st, ties_stop=ties_stop):
            V += m * X(s)
    return V
for r in (F(0), F(1, 2), F(3, 4), F(76, 100), F(1)):
    gs = ret_value(r, True) - ret_value(r, False)
    gc = ret_value(r, True, False) - ret_value(r, False, False)
    print(f"retention gain at r={r}: ties-stop {gs}, ties-continue {gc}")
    assert gs == (F(9, 200) if r <= F(3, 4) else F(0))
    assert gc == (F(9, 200) if r < F(3, 4) else F(0))
for r in (F(0), F(1, 3), F(1)):
    rv = lambda fk: r * value(F(1), fk, True) + (1 - r) * value(F(1), fk, False)
    assert rv(True) - rv(False) == (1 - r) * F(9, 200)
print("retention step (convention-dependent at r = 3/4 exactly) and randomized gain: ok")

# ---------------------------------------------------------------- T5 witness: least crossing index
nu, a0, a1, e, beta, c, h = F(9, 10), F(1, 10), F(1, 5), F(1, 10), F(9, 10), F(1), F(3, 2)
assert beta * e * h < a1 * (1 - e) * c
def crosses(n):
    w0 = nu * ((1 - e) * a0) ** n; w1 = (1 - nu) * ((1 - e) * a1) ** n
    return beta * e * h * (w0 + w1) < (w0 * a0 + w1 * a1) * (1 - e) * c
least = next(n for n in range(50) if crosses(n))
print("T5 least crossing index:", least); assert least == 4

# ---------------------------------------------------------------- T9 binding-cell posteriors
def post(eps_, aH, bH, aA, bA): return eps_ * bH * (1 - bA) / (eps_ * bH * (1 - bA) + (1 - eps_) * aH * (1 - aA))
assert post(F(1, 10), F(1, 10), F(9, 10), F(3, 10), F(7, 10)) == F(3, 10) >= F(1, 5)
assert post(F(1, 10), F(1, 10), F(9, 10), F(1, 10), F(9, 10)) == F(1, 10) < F(1, 5)
assert post(F(1, 10), F(1, 10), F(9, 10), F(1, 100), F(99, 100)) == F(1, 100) < F(1, 5)
print("T9 posteriors 3/10, 1/10, 1/100 (F9 right): ok")

# ---------------------------------------------------------------- T11 surgery Brier, T10 screening, P2, tripwire
mu = F(1, 2)
k = lambda w, o: F(9, 10) if w == o else F(1, 10)
Qs = lambda o, w: F(19, 20) if w == o else F(1, 20)
brier = sum(mu * k(w, o) * (Qs(o, True) - (1 if w else 0)) ** 2 for o in B for w in B)
assert brier == F(37, 400) <= F(1, 4)
def jA(e, al, be, ay, by, w, y, pr):
    return (e if w else 1 - e) * ((by if y else 1 - by) if w else (ay if y else 1 - ay)) * ((be if pr else 1 - be) if w else (al if pr else 1 - al))
args = (F(1, 10), F(1, 10), F(9, 10), F(1, 10), F(9, 10))
lhs = jA(*args, True, False, True) * sum(jA(*args, w, False, pr) for w in B for pr in B)
rhs = sum(jA(*args, True, False, pr) for pr in B) * sum(jA(*args, w, False, True) for w in B)
# NOTE (round 2): the Lean docstring, the report and both round-1 audits say "738/100000 ≠ 900/100000";
# the right-hand side is 9/10000 = 90/100000 (P(W, y=r) · P(y=r, Pr) = 1/100 · 9/100). The theorem
# `evidential_not_screened` carries no numeral and is true either way; the docstring numeral is wrong.
assert lhs == F(738, 100000) and rhs == F(9, 10000) and lhs != rhs
piP2 = [F(9, 20), F(1, 20), F(1, 10), F(2, 5)]; xq = [1, 0, 1, 0]
hrow = lambda w, h1, h2: h1 if w < 2 else h2
EU = sum(p * x for p, x in zip(piP2, xq)); assert EU == F(11, 20)
ER = sum(p * hrow(w, F(3, 5), F(2, 5)) for w, p in enumerate(piP2)); assert ER == F(1, 2)
assert EU - sum(p * hrow(w, F(9, 10), F(2, 5)) for w, p in enumerate(piP2)) == F(-1, 10)
assert piP2[0] == F(9, 20) != (piP2[0] + piP2[1]) * F(3, 5)          # reflection fails: 9/20 vs 3/10
assert sum(p * x * hrow(w, F(3, 5), F(2, 5)) for w, (p, x) in enumerate(zip(piP2, xq))) == F(31, 100)
assert sum(p * hrow(w, F(3, 5), F(2, 5)) ** 2 / 2 for w, p in enumerate(piP2)) == F(13, 100)
inf = sum(p * (x if w < 2 else F(13, 25)) for w, (p, x) in enumerate(zip(piP2, xq))); assert inf == F(71, 100)
assert F(1, 3) * (0 - 1) == F(-1, 3)                                  # tripwire cut at X = 1_{1}, s = 1
print("T11 37/400, T10 738 vs 90 /100000, P2 11/20 1/2 -1/10 9/20 31/100 13/100 71/100, tripwire -1/3: ok")
print("ALL CHECKS PASSED")
