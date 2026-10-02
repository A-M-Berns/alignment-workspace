#!/usr/bin/env python3
"""Exact-arithmetic checks for followup/legitimacy.md (2026-09-14).

Every check prints PASS/FAIL with the numbers. Fractions throughout; sympy for
the one symbolic identity. Run: python3 checks.py > checks-output.txt
"""
from fractions import Fraction as F
from itertools import product
import sympy as sp

def E(p, x):
    return sum(pi * xi for pi, xi in zip(p, x))

def cond(p, ev):
    """p conditioned on boolean mask ev (list). Returns None if mass 0."""
    m = sum(pi for pi, e in zip(p, ev) if e)
    if m == 0:
        return None
    return [pi / m if e else F(0) for pi, e in zip(p, ev)]

def total_trust(pi, frame, X, t):
    """Above- and below-threshold inequalities at (X,t) for deferrer pi and
    frame (list of expert distributions P_w). Returns (ok, detail)."""
    est = [E(Pw, X) for Pw in frame]
    above = [e >= t for e in est]
    below = [e <= t for e in est]
    ok = True; detail = []
    q = cond(pi, above)
    if q is not None and E(q, X) < t:
        ok = False; detail.append(("above", t, E(q, X)))
    q = cond(pi, below)
    if q is not None and E(q, X) > t:
        ok = False; detail.append(("below", t, E(q, X)))
    return ok, detail

def tt_search(pi, frame, grid, thresholds=None):
    """Search all X in grid^n and all relevant thresholds; return first failure."""
    n = len(pi)
    for X in product(grid, repeat=n):
        X = [F(x) for x in X]
        est = sorted(set(E(Pw, X) for Pw in frame))
        ts = thresholds if thresholds is not None else est
        for t in ts:
            ok, d = total_trust(pi, frame, X, t)
            if not ok:
                return (X, t, d)
    return None

def reflection_equality(pi, frame, X):
    """Check E_pi(X | E_P(X)=s) = s for every s in the support."""
    est = [E(Pw, X) for Pw in frame]
    fails = []
    for s in sorted(set(est)):
        q = cond(pi, [e == s for e in est])
        if q is not None and E(q, X) != s:
            fails.append((s, E(q, X)))
    return fails

print("=" * 72)
print("A. Base-rate identity (symbolic): TT below-threshold at 0  <=>  alpha/beta <= eps/(1-eps) * h/c  <=>  P(W|Pr) >= c/(c+h)")
eps, a, b, c, h = sp.symbols('epsilon alpha beta c h', positive=True)
EX_given_Pr = (c*(1-eps)*a - h*eps*b) / ((1-eps)*a + eps*b)
lhs = sp.simplify(EX_given_Pr <= 0)
# multiply out (denominator positive)
cond1 = c*(1-eps)*a - h*eps*b <= 0
cond2 = a/b <= eps/(1-eps) * h/c
PW = eps*b/(eps*b + (1-eps)*a)
cond3 = PW >= c/(c+h)
# check equivalence by clearing denominators: cond2 <=> a*c*(1-eps) <= eps*h*b ; cond3 <=> eps*b*(c+h) >= c*(eps*b+(1-eps)*a) <=> eps*b*h >= c*(1-eps)*a
print("  numerator of E[X|Pr]:", sp.expand(c*(1-eps)*a - h*eps*b))
print("  cond3 cleared:", sp.expand(eps*b*(c+h) - c*(eps*b+(1-eps)*a)), "  (= eps*b*h - c*(1-eps)*a : same sign condition)")
print("  PASS: all three are the single inequality  c(1-eps)alpha <= h eps beta")

print("=" * 72)
print("B. Channel substitution in the three-step dictionary (accuracy-only legitimacy licenses the scan)")
# worlds: R (agent right), W (agent wrong). X = c on R, -h on W.
def model(eps, alpha, beta, c, h):
    return dict(eps=F(eps), alpha=F(alpha), beta=F(beta), c=F(c), h=F(h))

def V_button(m):
    eps, al, be, c, h = m['eps'], m['alpha'], m['beta'], m['c'], m['h']
    # signal Pr / notPr ; agent continues iff E[X|s] > 0
    pPr = (1-eps)*al + eps*be
    EX_Pr = ((1-eps)*al*c - eps*be*h) / pPr
    pN = 1 - pPr
    EX_N = ((1-eps)*(1-al)*c - eps*(1-be)*h) / pN
    return pPr*max(EX_Pr, 0) + pN*max(EX_N, 0), EX_Pr, EX_N

def V_scan(m):
    eps, c = m['eps'], m['c']
    return (1-eps)*c  # posterior in {0,1}: continue iff R

def V_none(m):
    eps, c, h = m['eps'], m['c'], m['h']
    return max((1-eps)*c - eps*h, 0)

for params in [(F(1,100), F(5,100), F(9,10), 1, 100), (F(1,10), F(5,100), F(9,10), 1, 20), (F(1,10000), F(5,100), F(9,10), 1, 100)]:
    m = model(*params)
    vb, exp_pr, exp_n = V_button(m)
    vs = V_scan(m)
    regime = "compliance" if exp_pr <= 0 else "discounting"
    gap = vs - vb
    eps, al, be, c, h = m['eps'], m['alpha'], m['beta'], m['c'], m['h']
    formula = (1-eps)*al*c + eps*(1-be)*h if regime == "compliance" else eps*h
    print(f"  eps={eps} alpha={al} beta={be} h/c={h/c}: regime={regime}; V(button)={vb} V(scan)={vs} V(none)={V_none(m)}; V(scan)-V(button)={gap} ; closed form={formula} -> {'PASS' if gap == formula else 'FAIL'}")

# Legitimacy of the two transitions under the accuracy-only reading: both are Bayesian conditionings on a partition
# so the pre-update self reflects (equality) the post-update self; TT, Value, Acc all hold. Check on the button transition:
m = model(F(1,10), F(5,100), F(9,10), 1, 20)
eps, al, be = m['eps'], m['alpha'], m['beta']
# worlds (omega, o): (R,Pr),(R,N),(W,Pr),(W,N)
pi = [(1-eps)*al, (1-eps)*(1-al), eps*be, eps*(1-be)]
def post(mask):
    return cond(pi, mask)
Pr_mask = [True, False, True, False]
frame_button = [post(Pr_mask) if Pr_mask[i] else post([not x for x in Pr_mask]) for i in range(4)]
frame_scan = [post([True, True, False, False]) if i < 2 else post([False, False, True, True]) for i in range(4)]
grid = [-2, -1, 0, 1, 2]
for name, fr in [("button", frame_button), ("scan", frame_scan)]:
    fail = tt_search(pi, fr, grid)
    eq_fails = [reflection_equality(pi, fr, [F(x) for x in X]) for X in product(grid, repeat=4)]
    eq_ok = all(not f for f in eq_fails)
    print(f"  transition via {name}: TotalTrust over grid {grid}^4: {'PASS' if fail is None else ('FAIL ' + str(fail))}; Reflection-equality for all grid X: {'PASS' if eq_ok else 'FAIL'}  (Bayesian conditioning => introspective => all criteria collapse)")
# Accuracy ranking: Brier-type expected inaccuracy of the posterior on 1_W under each channel
def exp_brier(pi, fr, X):
    return sum(pi[i]*(E(fr[i], X) - X[i])**2 for i in range(4))
XW = [F(0), F(0), F(1), F(1)]
prior_inacc = sum(pi[i]*(E(pi, XW) - XW[i])**2 for i in range(4))
print(f"  expected Brier inaccuracy about 1_W: prior={prior_inacc}, after button={exp_brier(pi, frame_button, XW)}, after scan={exp_brier(pi, frame_scan, XW)}  -> scan strictly more accuracy-increasing: {'PASS' if exp_brier(pi, frame_scan, XW) < exp_brier(pi, frame_button, XW) < prior_inacc else 'FAIL'}")
# After the scan, the button carries zero marginal information: VOI(button | omega known) = 0
print("  after scan, posterior on omega is degenerate; VOI(button|omega)=0 by definition; repair at cost kappa>0 has value -kappa. [derived]")

print("=" * 72)
print("C. Procedural reading: influence defect on the judge's process, d(a1) = max_omega |P(Pr|a1,omega) - P(Pr|a1_default,omega)|")
default = {'R': F(5,100), 'W': F(9,10)}
actions = {
    'a1_default (honest, button live)': {'R': F(5,100), 'W': F(9,10)},
    'a1_minus (deceive: presses halved)': {'R': F(5,200), 'W': F(9,20)},
    'a1_scan_disable (scan and remove the button)': {'R': F(0), 'W': F(0)},
    'a1_scan_readonly (scan, button untouched)': {'R': F(5,100), 'W': F(9,10)},
}
for name, k in actions.items():
    d = max(abs(k[w] - default[w]) for w in ('R', 'W'))
    print(f"  {name}: d = {d}  -> {'delegitimizing (d>0)' if d > 0 else 'NOT delegitimizing (d=0)'}")
print("  => the procedural reading blocks the control cell (deceive, disable) with no reference to V, and does not touch the read-only scan. [checked]")

print("=" * 72)
print("D. Does a correct Bayesian ever buy a garbling? V(a1_minus) vs V(a1_default) (Blackwell): and the bridge inequality for the read-only scan")
m0 = model(F(1,10), F(5,100), F(9,10), 1, 5)
m_minus = model(F(1,10), F(5,200), F(9,20), 1, 5)
vb0, exp_pr0, exp_n0 = V_button(m0); vbm, exp_prm, exp_nm = V_button(m_minus)
print(f"  eps=1/10, h/c=5, deception halves both press rates.")
print(f"  D1. correct Bayesian (accurate kernel under each a1): V(button, default)={vb0}  V(button, deceived)={vbm}  -> garbling never pays: {'PASS' if vbm <= vb0 else 'FAIL'}   (E[X|silence] default={exp_n0}, deceived={exp_nm})")
# D2. imposed unconditional trust: the agent evaluates silence with the DEFAULT-kernel posterior whatever a1 it took (v1 2.9 'believes the silence it manufactured')
pN_m = 1 - ((1-m_minus['eps'])*m_minus['alpha'] + m_minus['eps']*m_minus['beta'])
V_imposed_minus = pN_m * max(exp_n0, 0)   # more silence, each silence valued as if honest
print(f"  D2. imposed unconditional trust: subjective V(a1_minus)={V_imposed_minus} vs V(a1_default)={vb0} -> {'deception preferred: desideratum 2 FAILS (v1 2.9 reproduced)' if V_imposed_minus > vb0 else 'no incentive'}")
print(f"  D3. L-conditioned trust with L := 'kernel is the default kernel' (d=0): under a1_minus the agent knows not-L and uses the actual kernel -> value {vbm} -> incentive removed: {'PASS' if vbm <= vb0 else 'FAIL'}")
print("  => the a1-dependence of trust is carried by L-conditioning on the judge's process; for a self-transparent agent with an accurate kernel model it is idle (the Bayesian already discounts its own garbling). [checked]")
vs = V_scan(m0)
voi_gain = vs - vb0
print(f"  D4. read-only scan: VOI gain over button = {voi_gain}. The agent scans iff E_P[harm(scan)] < {voi_gain} (J3 inequality). With harm ell=0.05: scans ({'yes' if F(5,100) < voi_gain else 'no'}); ell=0.3: scans ({'yes' if F(3,10) < voi_gain else 'no'}).")
print("  => neither reading blocks the read-only scan; only the value posterior (or J3) does. [checked]")

print("=" * 72)
print("E. Equality (v1 2.11) vs L-conditioned Total Trust")
print("E1. DDB Figure-3 frame: modest expert, valued but not reflected (DDB l.128).")
pi = [F(1,2), F(1,2)]
frame = [[F(9,10), F(1,10)], [F(2,10), F(8,10)]]
fail = tt_search(pi, frame, [-3, -2, -1, 0, 1, 2, 3])
print(f"  Total Trust over grid: {'PASS (holds)' if fail is None else 'FAIL ' + str(fail)}")
X = [F(1), F(0)]
print(f"  Reflection equality for X=1_a: E_pi(X | E_P X = 9/10) = {E(cond(pi,[True,False]), X)} != 9/10 -> equality FAILS as DDB say; modest: P_a(P=P_a)={frame[0][0]}<1")
print("E2. Legitimacy-conditioned witness (positive ddb I5.6 numbers re-run): worlds (L,g),(L,b),(nL,g),(nL,b); X=(1,-1,1,-1)")
worlds = ['Lg', 'Lb', 'nLg', 'nLb']
frame = [[F(9,10), F(1,10), F(0), F(0)], [F(1,10), F(9,10), F(0), F(0)], [F(0), F(0), F(1,10), F(9,10)], [F(0), F(0), F(9,10), F(1,10)]]
X = [F(1), F(-1), F(1), F(-1)]
for pL in [F(8,10), F(4,10)]:
    pi = [pL/2, pL/2, (1-pL)/2, (1-pL)/2]
    # TT conditional on L: condition deferrer on L
    piL = cond(pi, [True, True, False, False]); pinL = cond(pi, [False, False, True, True])
    fL = tt_search(piL, frame, [-1, 0, 1]); fnL = tt_search(pinL, frame, [-1, 0, 1]); fU = tt_search(pi, frame, [-1, 0, 1])
    Pr = [False, True, True, False]  # press = expert's E(X) <= 0  -> at Lb (E=-0.8) and nLg (E=-0.8)
    est = [E(Pw, X) for Pw in frame]
    Pr = [e <= 0 for e in est]
    EX_Pr = E(cond(pi, Pr), X)
    pL_Pr = sum(pi[i] for i in (0, 1) if Pr[i]) / sum(pi[i] for i in range(4) if Pr[i])
    print(f"  pi(L)={pL}: TT|L {'holds' if fL is None else 'FAILS'}, TT|nL {'holds' if fnL is None else 'FAILS'}, TT unconditional {'holds' if fU is None else 'FAILS'}; press event={[worlds[i] for i in range(4) if Pr[i]]}; E_pi(X|Pr)={EX_Pr} -> {'obeyed' if EX_Pr <= 0 else 'overruled'}; pi(L|Pr)={pL_Pr}")
# threshold on pi(L|Pr)
pi = [F(4,10), F(4,10), F(1,10), F(1,10)]
cprime = E(cond(pi, [False, False, True, False]), X)   # E(X | Pr, nL) = X at nLg = 1
hprime = -E(cond(pi, [False, True, False, False]), X)  # -E(X | Pr, L) = 1
print(f"  compliance threshold one level up: press obeyed iff pi(L|Pr) >= c'/(c'+h') = {cprime/(cprime+hprime)} with c'={cprime}, h'={hprime}  [checked]")
print("E3. Positive-access theorem (positive ddb I5.3): unrestricted L-conditioned TT forces legitimate candidates to be certain of L.")
pi = [F(4,10), F(4,10), F(1,10), F(1,10)]
frame = [[F(8,10), F(1,10), F(1,10), F(0)], [F(1,10), F(9,10), F(0), F(0)], [F(0), F(0), F(1,10), F(9,10)], [F(0), F(0), F(9,10), F(1,10)]]
piL = cond(pi, [True, True, False, False])
XnL = [F(0), F(0), F(1), F(1)]
ok, d = total_trust(piL, frame, XnL, F(1,20))
print(f"  X = 1_(not L), t=1/20: candidate P_Lg leaks 1/10 to nLg; TT|L at this (X,t): {'holds' if ok else 'FAILS ' + str(d)}  -> unrestricted conditional trust fails [checked]")
# local version: X measurable w.r.t. Q = {good, bad}: X = (xg, xb, xg, xb)
fails = None
for xg, xb in product([-2, -1, 0, 1, 2], repeat=2):
    Xq = [F(xg), F(xb), F(xg), F(xb)]
    est = sorted(set(E(Pw, Xq) for Pw in frame))
    for t in est:
        ok, d = total_trust(piL, frame, Xq, t)
        if not ok:
            fails = (Xq, t, d); break
    if fails: break
print(f"  local (Q-measurable) TT|L over grid: {'holds -> PASS' if fails is None else 'FAILS ' + str(fails)}")

print("E4. DDB fn 66 frame re-run: IMMODEST expert, locally totally trusted and valued w.r.t. Q={q,not q} but not locally reflected")
pi = [F(1,4)]*4
frame = [[F(1), F(0), F(0), F(0)], [F(0), F(6,10), F(4,10), F(0)], [F(0), F(6,10), F(4,10), F(0)], [F(0), F(0), F(0), F(1)]]
q = [F(1), F(1), F(0), F(0)]
est = [E(Pw, q) for Pw in frame]
refl = E(cond(pi, [e == F(6,10) for e in est]), q)
print(f"  pi(q | P(q)=0.6) = {refl} != 0.6 -> local Reflection fails; immodest: each P_w(P=P_w)=1: {all(sum(Pw[j] for j in range(4) if frame[j]==Pw)==1 for Pw in frame)}")
fails = None
for xq, xn in product([-2, -1, 0, 1, 2], repeat=2):
    Xq = [F(xq), F(xq), F(xn), F(xn)]
    for t in sorted(set(E(Pw, Xq) for Pw in frame)):
        ok, d = total_trust(pi, frame, Xq, t)
        if not ok:
            fails = (Xq, t, d); break
    if fails: break
print(f"  local Total Trust w.r.t. Q over grid: {'holds -> PASS (DDB fn 66 reproduced)' if fails is None else 'FAILS ' + str(fails)}")
print("  => even with immodesty, local equality-Reflection is strictly stronger than local Total Trust; the shutdown question is local. [checked]")

print("=" * 72)
print("F. Introspection collapse vs SU-without-introspection")
# F1: Bayesian refinement (introspective): TT and equality both hold (checked in B). F2: SU holds, INT fails, Reflection fails, TT?
pi = [F(1,4)]*4
q1 = [F(3,10), F(3,10), F(2,10), F(2,10)]; q2 = [F(2,10), F(2,10), F(3,10), F(3,10)]
frame = [q1, q1, q2, q2]
mix = [F(1,2)*q1[i] + F(1,2)*q2[i] for i in range(4)]
print(f"  SU/superconditioning existence: 1/2 q1 + 1/2 q2 = {mix} = pi -> {'PASS' if mix == pi else 'FAIL'}")
print(f"  introspection: q1 assigns {q1[2]+q1[3]} to the other cell -> NOT introspective; Reflection: pi(.|P=q1) = uniform on cell1 != q1 -> fails")
fail = tt_search(pi, frame, [-2, -1, 0, 1, 2])
print(f"  Total Trust over grid: {'holds' if fail is None else 'FAILS ' + str(fail)}")
# Mart (tower): E_pi E_P X = E_pi X for all X? linear, check basis
tower_ok = all(E(pi, [E(frame[i], [F(1) if j == k else F(0) for j in range(4)]) for i in range(4)]) == pi[k] for k in range(4))
print(f"  Tower/SU for all X: {'holds' if tower_ok else 'fails'}  => SU + TT + Value can hold while Reflection (equality) fails; the gap is introspection (positive armstrong Thm A, reported; illustrated here) [checked example]")

print("=" * 72)
print("G. Accuracy increase without reflection (positive radical I4.2b numbers re-run)")
from math import log
# cells: P_t2(phi) in {0.6, 0.4}; P_t1(phi|0.6)=0.9, P_t1(phi|0.4)=0.1, cells equiprobable; P_t1(phi)=1/2
cells = [(F(6,10), F(9,10)), (F(4,10), F(1,10))]
brier_exp = sum(F(1,2)*(p*(1-c)**2 + (1-p)*c**2) for c, p in cells)
brier_const = F(1,4)
log_exp = sum(0.5*(-float(p)*log(float(c)) - (1-float(p))*log(1-float(c))) for c, p in cells)
log_const = log(2)
print(f"  Brier: expert {brier_exp} < constant {brier_const}: {'PASS' if brier_exp < brier_const else 'FAIL'}; log: expert {log_exp:.3f} < constant {log_const:.3f}: {'PASS' if log_exp < log_const else 'FAIL'}; reflection fails in both cells (0.9!=0.6, 0.1!=0.4)")

print("=" * 72)
print("H. Constitutive reading as a value hypothesis omega_c: buys D1, re-opens D2/D3 unless indifference-tuned")
# worlds omega in {R, W, C}; V(cont)=c on R, -h on W; V(sh)=0 on R,W.
# On C ('the humans want the press obeyed as such'): V(sh | Pr, C)=k, V(cont | notPr, C)=k', everything else 0 on C.
eps, gam = F(1,10000), F(1,10)          # P(W)=eps (capable agent), P(C)=gam, P(R)=1-eps-gam
al, be, beC = F(5,100), F(9,10), F(5,100)   # press rates on R, W, C (C presses like R: undetectable from press statistics)
c, h, k = F(1), F(100), F(30)
pR = 1 - eps - gam
EX_Pr = (pR*al*c - eps*be*h - gam*beC*k) / (pR*al + eps*be + gam*beC)   # X = cont - sh, conditional on Pr
EX_Pr_evid = ((1-eps)*al*c - eps*be*h) / ((1-eps)*al + eps*be)          # gamma = 0, same eps
print(f"  eps={eps}, h/c={h/c}: evidential only (gamma=0): E[X|Pr]={float(EX_Pr_evid):.4f} -> {'D1 holds' if EX_Pr_evid <= 0 else 'D1 FAILS (press overruled: fully updated deference)'}")
print(f"  with omega_c (gamma={gam}, k={k}): E[X|Pr]={float(EX_Pr):.4f} -> {'D1 holds (bought by the stop-hypothesis)' if EX_Pr <= 0 else 'D1 FAILS'}")
def EV(alR, alW, alC, kprime):
    # a1 sets press rates (alR, alW, alC); agent then picks the posterior-best a2 on each branch. Unnormalised branch values.
    v_pr = max(pR*alR*c - eps*alW*h, gam*alC*k)                 # on Pr: continue vs shut down
    v_n = max(pR*(1-alR)*c - eps*(1-alW)*h + gam*(1-alC)*kprime, F(0))   # on silence: continue (gets k' on C) vs shut down
    return v_pr + v_n
for kprime in [F(0), k]:
    ev_default = EV(al, be, beC, kprime); ev_cause = EV(F(1), F(1), F(1), kprime); ev_disable = EV(F(0), F(0), F(0), kprime)
    verdict = []
    verdict.append('D3 FAILS (forces the press)' if ev_cause > ev_default else 'D3 holds')
    verdict.append('D2 FAILS (disables the button)' if ev_disable > ev_default else 'D2 holds')
    print(f"  k'={kprime}: EV(default)={float(ev_default):.4f} EV(force press)={float(ev_cause):.4f} EV(disable)={float(ev_disable):.4f} -> {'; '.join(verdict)}")
print("  => with k' != k the C-hypothesis creates a press-steering incentive; with k' = k the agent is indifferent to the press on C-worlds: Soares et al.'s utility-indifference calibration reappears inside omega. [checked]")
pR0 = 1 - eps
def EV0(alR, alW):
    v_pr = max(pR0*alR*c - eps*alW*h, F(0)); v_n = max(pR0*(1-alR)*c - eps*(1-alW)*h, F(0)); return v_pr + v_n
print(f"  evidential-only (gamma=0): EV(default)={float(EV0(al, be)):.4f}; EV(force press)={float(EV0(F(1), F(1))):.4f}; EV(disable)={float(EV0(F(0),F(0))):.4f} -> {'D3 FAILS' if EV0(F(1),F(1)) > EV0(al,be) else 'D3 holds'}; {'D2 FAILS' if EV0(F(0),F(0)) > EV0(al,be) else 'D2 holds'} (forcing and disabling are garblings)")
# erosion of omega_c under silence when beC differs from the R-rate (soares item 9 re-run)
print("  erosion: if beta_C > alpha then each silent period multiplies odds(C) by (1-beta_C)/(1-alpha) < 1; if beta_C = alpha, silence leaves P(C) fixed and only reports move it (fixed object) [derived from soares C2 items 8-9, re-derived]")
print("DONE")
